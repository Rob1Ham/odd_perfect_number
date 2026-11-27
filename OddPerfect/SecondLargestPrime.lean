module

public import OddPerfect.AcquaahKonyagin
public import OddPerfect.Reciprocal
public import OddPerfect.NearPerfect
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Zelinsky's second-largest prime bound and Bibby–Vyncke–Zelinsky's top-3 prime product bound

Formalization of:
1. `prime_pow_five_lt_two_mul_of_lt`: for any `b < c` in `N.primeFactors`, `b ^ 5 < 2 * N`.
2. `prime_triple_prod_pow_five_lt`: for any `a < b < c` in `N.primeFactors`, `(a * b * c) ^ 5 < (2 * N) ^ 3`.
3. Ranked corollaries for the largest, second-largest, and third-largest prime factors of `N`
   via `Finset.max'` and `Finset.erase`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma nat_coprime_mul_dvd {a b c : ℕ} (hcop : a.Coprime b) (ha : a ∣ c) (hb : b ∣ c) :
    a * b ∣ c := by
  obtain ⟨k, rfl⟩ := ha
  exact mul_dvd_mul_left a (hcop.symm.dvd_of_dvd_mul_left hb)

private lemma even_pos_eq_two_or_four_le {e : ℕ} (he0 : 0 < e) (heven : Even e) :
    e = 2 ∨ 4 ≤ e := by
  rcases heven with ⟨k, rfl⟩
  omega

private lemma sigma_lt_two_mul_of_coprime_cofactor {N A B : ℕ} (hN : N.Perfect)
    (hNAB : N = A * B) (hcop : A.Coprime B) (hB : 1 < B) :
    sigma 1 A < 2 * A := by
  have hsig : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
  have hmul : sigma 1 A * sigma 1 B = 2 * A * B := by
    rw [← isMultiplicative_sigma.map_mul_of_coprime hcop, ← hNAB, hsig, hNAB]
    ring
  have hA0 : A ≠ 0 := by rintro rfl; simp at hNAB; exact hN.2.ne' hNAB
  have hsigA : 0 < sigma 1 A := sigma_pos 1 A hA0
  have hB_lt : B < sigma 1 B := self_lt_sigma_of_one_lt hB
  have hlt : sigma 1 A * B < 2 * A * B := by
    calc sigma 1 A * B < sigma 1 A * sigma 1 B := Nat.mul_lt_mul_of_pos_left hB_lt hsigA
      _ = 2 * A * B := hmul
  exact Nat.lt_of_mul_lt_mul_right hlt

private lemma primeFactors_sdiff_decomp {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (s : Finset ℕ) (hs : s ⊆ N.primeFactors) (hne : s.Nonempty) (hs_lt : s.card < N.primeFactors.card) :
    let A := ∏ p ∈ s, p ^ N.factorization p
    let K := ∏ p ∈ N.primeFactors \ s, p ^ N.factorization p
    N = A * K ∧ A.Coprime K ∧ 1 < K ∧ Odd K ∧
      sigma 1 A = (∏ p ∈ s, sigma 1 (p ^ N.factorization p)) ∧
      sigma 1 K < 2 * K ∧
      (∏ p ∈ s, sigma 1 (p ^ N.factorization p)) * sigma 1 K = 2 * N := by
  intro A K
  have hn : N ≠ 0 := hN.2.ne'
  have hprod : N = A * K := by
    calc N = ∏ p ∈ N.primeFactors, p ^ N.factorization p :=
          Nat.prod_primeFactors_pow_factorization hn
      _ = (∏ p ∈ N.primeFactors \ s, p ^ N.factorization p) *
            (∏ p ∈ s, p ^ N.factorization p) := (Finset.prod_sdiff hs).symm
      _ = A * K := mul_comm _ _
  have hcop : A.Coprime K := by
    refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun r hr => ?_
    have hp_prime := Nat.prime_of_mem_primeFactors (hs hp)
    have hr_prime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hr).1
    have hpr : p ≠ r := fun h => (Finset.mem_sdiff.mp hr).2 (h ▸ hp)
    exact ((Nat.coprime_primes hp_prime hr_prime).mpr hpr).pow _ _
  have hsdiff_ne : (N.primeFactors \ s).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hs]
    omega
  have hK1 : 1 < K := by
    obtain ⟨r, hr⟩ := hsdiff_ne
    have hr_mem := (Finset.mem_sdiff.mp hr).1
    have hr_prime := Nat.prime_of_mem_primeFactors hr_mem
    have hr_pos : 0 < N.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr_mem)
    have h1 : 1 < r ^ N.factorization r := one_lt_pow₀ hr_prime.one_lt hr_pos.ne'
    have hdvd : r ^ N.factorization r ∣ K := Finset.dvd_prod_of_mem _ hr
    have hKpos : 0 < K := Finset.prod_pos fun u hu =>
      pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hu).1).pos _
    exact h1.trans_le (Nat.le_of_dvd hKpos hdvd)
  have hKodd : Odd K := ho.of_dvd_nat ⟨A, by rw [hprod, mul_comm]⟩
  have hA1 : 1 < A := by
    obtain ⟨p, hp⟩ := hne
    have hp_prime := Nat.prime_of_mem_primeFactors (hs hp)
    have hp_pos : 0 < N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (hs hp))
    have h1 : 1 < p ^ N.factorization p := one_lt_pow₀ hp_prime.one_lt hp_pos.ne'
    have hdvd : p ^ N.factorization p ∣ A := Finset.dvd_prod_of_mem _ hp
    have hApos : 0 < A := Finset.prod_pos fun u hu =>
      pow_pos (Nat.prime_of_mem_primeFactors (hs hu)).pos _
    exact h1.trans_le (Nat.le_of_dvd hApos hdvd)
  have hsigA : sigma 1 A = ∏ p ∈ s, sigma 1 (p ^ N.factorization p) := by
    refine ArithmeticFunction.IsMultiplicative.map_prod _ isMultiplicative_sigma s ?_
    intro i hi j hj hij
    exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (hs hi))
      (Nat.prime_of_mem_primeFactors (hs hj))).mpr hij).pow _ _
  have hsigK : sigma 1 K < 2 * K :=
    sigma_lt_two_mul_of_coprime_cofactor hN (hprod.trans (mul_comm A K)) hcop.symm hA1
  have hsig_eq : (∏ p ∈ s, sigma 1 (p ^ N.factorization p)) * sigma 1 K = 2 * N := by
    rw [← hsigA, ← isMultiplicative_sigma.map_mul_of_coprime hcop, ← hprod, sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN
  exact ⟨hprod, hcop, hK1, hKodd, hsigA, hsigK, hsig_eq⟩

private lemma odd_prime_add_two_le_of_lt {N b c : ℕ} (ho : Odd N)
    (hbN : b ∈ N.primeFactors) (hcN : c ∈ N.primeFactors) (hbc : b < c) :
    3 ≤ b ∧ b + 2 ≤ c := by
  have hb_prime := Nat.prime_of_mem_primeFactors hbN
  have hb_odd : Odd b := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hbN)
  have hc_odd : Odd c := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hcN)
  have hb3 : 3 ≤ b := by
    have := hb_prime.two_le
    have := hb_odd.not_two_dvd_nat
    omega
  have hbc2 : b + 2 ≤ c := by
    rcases hb_odd with ⟨kb, rfl⟩
    rcases hc_odd with ⟨kc, rfl⟩
    omega
  exact ⟨hb3, hbc2⟩

private lemma odd_coprime_prime_self_sq_add_self_add_one {p : ℕ} (hp : p.Prime) :
    p.Coprime (p ^ 2 + p + 1) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hd1 : p ∣ 1 := (Nat.dvd_add_iff_right (dvd_add (dvd_pow_self p (by decide)) (dvd_refl p))).mpr hd
  exact hp.not_dvd_one hd1

private lemma pair_e1_e2_bound {N b c : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hbN : b ∈ N.primeFactors) (hcN : c ∈ N.primeFactors) (hbc : b < c)
    (heb : N.factorization b = 1) (hec : N.factorization c = 2) :
    b * c ^ 4 < 2 * N := by
  have hb_prime := Nat.prime_of_mem_primeFactors hbN
  have hc_prime := Nat.prime_of_mem_primeFactors hcN
  have ⟨_hb3, hbc2⟩ := odd_prime_add_two_le_of_lt ho hbN hcN hbc
  let s : Finset ℕ := {b, c}
  have hs_sub : s ⊆ N.primeFactors := by
    intro x hx
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hs_card : s.card < N.primeFactors.card := by
    have h4 := four_le_distinct_prime_factor_count ho hN
    have hsc : s.card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨hprod, _hcop, hK1, _hKodd, _hsigA, hsigK, hsig_eq⟩ :=
    primeFactors_sdiff_decomp ho hN s hs_sub (Finset.insert_nonempty _ _) hs_card
  set K := ∏ p ∈ N.primeFactors \ s, p ^ N.factorization p
  have hA_eq : (∏ p ∈ s, p ^ N.factorization p) = b * c ^ 2 := by
    rw [Finset.prod_pair hbc.ne, heb, hec, pow_one]
  have hsigA_eq : (∏ p ∈ s, sigma 1 (p ^ N.factorization p)) = (b + 1) * (c ^ 2 + c + 1) := by
    rw [Finset.prod_pair hbc.ne, heb, hec,
      sigma_one_apply_prime_pow hb_prime, sigma_one_apply_prime_pow hc_prime]
    simp [Finset.sum_range_succ]
    ring
  rw [hA_eq] at hprod
  rw [hsigA_eq, hprod] at hsig_eq
  have hdvd : c ^ 2 ∣ (b + 1) * (c ^ 2 + c + 1) * sigma 1 K :=
    ⟨2 * b * K, by linarith⟩
  have hcop1 : c.Coprime (b + 1) := by
    apply hc_prime.coprime_iff_not_dvd.mpr
    intro hd
    have hle := Nat.le_of_dvd (Nat.succ_pos b) hd
    omega
  have hcop2 : c.Coprime (c ^ 2 + c + 1) := odd_coprime_prime_self_sq_add_self_add_one hc_prime
  have hc2_dvd : c ^ 2 ∣ sigma 1 K := ((hcop1.mul_right hcop2).pow_left 2).dvd_of_dvd_mul_left hdvd
  have hKpos : 0 < K := by omega
  have hsigK_pos : 0 < sigma 1 K := sigma_pos 1 K hKpos.ne'
  have hc2_lt : c ^ 2 < 2 * K := (Nat.le_of_dvd hsigK_pos hc2_dvd).trans_lt hsigK
  have hbc2_pos : 0 < b * c ^ 2 := Nat.mul_pos hb_prime.pos (pow_pos hc_prime.pos 2)
  calc b * c ^ 4 = (b * c ^ 2) * c ^ 2 := by ring
    _ < (b * c ^ 2) * (2 * K) := Nat.mul_lt_mul_of_pos_left hc2_lt hbc2_pos
    _ = 2 * N := by rw [hprod]; ring

private lemma case_ec1_eb2_setup {N b c : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hbN : b ∈ N.primeFactors) (hcN : c ∈ N.primeFactors) (hbc : b < c)
    (heb : N.factorization b = 2) (hec : N.factorization c = 1) :
    ∃ K i : ℕ, 1 < K ∧ Odd K ∧ b.Coprime K ∧ c.Coprime K ∧
      N = c * b ^ 2 * K ∧ sigma 1 K < 2 * K ∧ 0 < i ∧
      (b ^ 2 + b + 1) * sigma 1 K = c * i ∧ (c + 1) * i = 2 * b ^ 2 * K := by
  have hb_prime := Nat.prime_of_mem_primeFactors hbN
  have hc_prime := Nat.prime_of_mem_primeFactors hcN
  let s : Finset ℕ := {b, c}
  have hs_sub : s ⊆ N.primeFactors := by
    intro x hx
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hs_card : s.card < N.primeFactors.card := by
    have h4 := four_le_distinct_prime_factor_count ho hN
    have hsc : s.card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨hprod, hcop, hK1, hKodd, _hsigA, hsigK, _hsig_eq⟩ :=
    primeFactors_sdiff_decomp ho hN s hs_sub (Finset.insert_nonempty _ _) hs_card
  set K := ∏ p ∈ N.primeFactors \ s, p ^ N.factorization p
  have hA_eq : (∏ p ∈ s, p ^ N.factorization p) = b ^ 2 * c := by
    rw [Finset.prod_pair hbc.ne, heb, hec, pow_one]
  rw [hA_eq] at hprod
  rw [hA_eq] at hcop
  have hbc_cop : b.Coprime c := (Nat.coprime_primes hb_prime hc_prime).mpr hbc.ne
  have hcop_bK : b.Coprime K := Nat.Coprime.coprime_dvd_left ⟨b * c, by ring⟩ hcop
  have hcop_cK : c.Coprime K := Nat.Coprime.coprime_dvd_left (dvd_mul_left c (b ^ 2)) hcop
  have hN_form : N = c ^ 1 * (b ^ 2 * K) := by rw [pow_one, hprod]; ring
  have hc_ndvd : ¬ c ∣ b ^ 2 * K := by
    intro hd
    have hcop_c : c.Coprime (b ^ 2 * K) := (hbc_cop.symm.pow_right 2).mul_right hcop_cK
    have hc1 : c = 1 := by simpa using hcop_c.coprime_dvd_right hd
    exact hc_prime.ne_one hc1
  obtain ⟨i, hi0, hi1, hi2, _⟩ := exists_component_index hN hc_prime hN_form hc_ndvd
  have hsig_bK : sigma 1 (b ^ 2 * K) = (b ^ 2 + b + 1) * sigma 1 K := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (hcop_bK.pow_left 2),
      sigma_one_apply_prime_pow hb_prime]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
    ring
  have hsig_c1 : sigma 1 (c ^ 1) = c + 1 := by
    rw [sigma_one_apply_prime_pow hc_prime]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
    ring
  rw [hsig_bK, pow_one] at hi1
  rw [hsig_c1] at hi2
  refine ⟨K, i, hK1, hKodd, hcop_bK, hcop_cK, by rw [hprod]; ring, hsigK, hi0, hi1, by linarith⟩

private lemma case_ec1_eb2_mid_dvd {b c K i : ℕ} (hb_prime : b.Prime) (hc_prime : c.Prime)
    (hb_odd : Odd b) (hc_odd : Odd c) (hK1 : 1 < K) (hsigK : sigma 1 K < 2 * K)
    (hi1 : (b ^ 2 + b + 1) * sigma 1 K = c * i) (hi2 : (c + 1) * i = 2 * b ^ 2 * K)
    (hbi : b ∣ i) (hb2i : ¬ b ^ 2 ∣ i) :
    b * c < 2 * K := by
  obtain ⟨i0, rfl⟩ := hbi
  have hbi0 : ¬ b ∣ i0 := fun h => hb2i (by rw [pow_two]; exact mul_dvd_mul_left b h)
  have hb_dvd_sig : b ∣ sigma 1 K := by
    have hb_mul : b ∣ (b ^ 2 + b + 1) * sigma 1 K := by rw [hi1]; exact ⟨c * i0, by ring⟩
    exact (odd_coprime_prime_self_sq_add_self_add_one hb_prime).dvd_of_dvd_mul_left hb_mul
  obtain ⟨s, hs⟩ := hb_dvd_sig
  have hs_pos : 0 < s := by
    have hK0 : K ≠ 0 := by omega
    have := sigma_pos 1 K hK0
    rw [hs] at this
    exact Nat.pos_of_mul_pos_left this
  have h_eq1 : (b ^ 2 + b + 1) * s = c * i0 := by
    apply Nat.mul_left_cancel hb_prime.pos
    calc b * ((b ^ 2 + b + 1) * s) = (b ^ 2 + b + 1) * (b * s) := by ring
      _ = (b ^ 2 + b + 1) * sigma 1 K := by rw [hs]
      _ = c * (b * i0) := hi1
      _ = b * (c * i0) := by ring
  have h_eq2 : (c + 1) * i0 = 2 * b * K := by
    apply Nat.mul_left_cancel hb_prime.pos
    calc b * ((c + 1) * i0) = (c + 1) * (b * i0) := by ring
      _ = 2 * b ^ 2 * K := hi2
      _ = b * (2 * b * K) := by ring
  have hb_dvd_cp1 : b ∣ c + 1 := by
    have h1 : b ∣ (c + 1) * i0 := by rw [h_eq2]; exact ⟨2 * K, by ring⟩
    exact (hb_prime.coprime_iff_not_dvd.mpr hbi0).dvd_of_dvd_mul_right h1
  have h2_dvd_cp1 : 2 ∣ c + 1 := by
    rcases hc_odd with ⟨kc, rfl⟩
    exact ⟨kc + 1, by ring⟩
  have h2b_dvd_cp1 : 2 * b ∣ c + 1 :=
    nat_coprime_mul_dvd (hb_odd.coprime_two_right.symm) h2_dvd_cp1 hb_dvd_cp1
  obtain ⟨k, hk⟩ := h2b_dvd_cp1
  have hk_pos : 0 < k := by
    by_contra h0
    have : k = 0 := by omega
    subst this
    simp at hk
  have hK_eq : K = k * i0 := by
    apply Nat.mul_left_cancel (Nat.mul_pos (by decide : 0 < 2) hb_prime.pos)
    calc 2 * b * K = (c + 1) * i0 := h_eq2.symm
      _ = 2 * b * (k * i0) := by rw [hk]; ring
  have hc_ndvd : ¬ c ∣ b ^ 2 + b + 1 := by
    intro hcd
    obtain ⟨d, hd⟩ := hcd
    have hd_pos : 0 < d := by
      by_contra h0
      have : d = 0 := by omega
      subst this
      simp at hd
    have hodd_sum : Odd (b ^ 2 + b + 1) := by
      rcases hb_odd with ⟨kb, rfl⟩
      refine ⟨2 * kb ^ 2 + 3 * kb + 1, by ring⟩
    have hd_odd : Odd d := hodd_sum.of_dvd_nat ⟨c, by rw [hd, mul_comm]⟩
    have hi0_eq : i0 = d * s := by
      apply Nat.mul_left_cancel hc_prime.pos
      calc c * i0 = (b ^ 2 + b + 1) * s := h_eq1.symm
        _ = c * (d * s) := by rw [hd]; ring
    have hK_lt_sig : K < sigma 1 K := self_lt_sigma_of_one_lt hK1
    nth_rw 1 [hK_eq, hi0_eq] at hK_lt_sig
    rw [hs] at hK_lt_sig
    have hkd_lt : k * d < b := Nat.lt_of_mul_lt_mul_right (by simpa [mul_assoc] using hK_lt_sig)
    have hd_lt : d < b := lt_of_le_of_lt (Nat.le_mul_of_pos_left d hk_pos) hkd_lt
    have hrel : 2 * k * d * b = b ^ 2 + b + 1 + d := by
      calc 2 * k * d * b = (2 * b * k) * d := by ring
        _ = (c + 1) * d := by rw [hk]
        _ = c * d + d := by ring
        _ = b ^ 2 + b + 1 + d := by rw [hd]
    have hb_dvd_1d : b ∣ 1 + d := by
      have : b ∣ b ^ 2 + b + (1 + d) := by
        rw [show b ^ 2 + b + (1 + d) = 2 * k * d * b by omega]
        exact dvd_mul_left b _
      exact (Nat.dvd_add_iff_right (dvd_add (dvd_pow_self b (by decide)) (dvd_refl b))).mpr this
    have hle := Nat.le_of_dvd (by positivity) hb_dvd_1d
    have h1d_eq : 1 + d = b := by omega
    rcases hb_odd with ⟨kb, hkb⟩
    rcases hd_odd with ⟨kd, hkd⟩
    omega
  have hc_dvd_s : c ∣ s := by
    have hcs : c ∣ (b ^ 2 + b + 1) * s := by rw [h_eq1]; exact dvd_mul_right c i0
    exact (hc_prime.coprime_iff_not_dvd.mpr hc_ndvd).dvd_of_dvd_mul_left hcs
  have hcs_le : c ≤ s := Nat.le_of_dvd hs_pos hc_dvd_s
  calc b * c ≤ b * s := Nat.mul_le_mul_left b hcs_le
    _ = sigma 1 K := hs.symm
    _ < 2 * K := hsigK

private lemma case_ec1_eb2_not_dvd_poly {b c : ℕ} (hb3 : 3 ≤ b) (hc_ge : 2 * b ^ 2 ≤ c + 1) :
    b ^ 3 * (c * b + c + b ^ 2 + b + 1) < c * (c + 1) * (b ^ 2 + b + 1) := by
  let d : ℕ := c + 1 - 2 * b ^ 2
  have hd_eq : c + 1 = 2 * b ^ 2 + d := by omega
  have hc_pos : 0 < c := by
    have : 9 ≤ b ^ 2 := by nlinarith
    omega
  zify
  have hcz : (c : ℤ) = 2 * (b : ℤ) ^ 2 + (d : ℤ) - 1 := by
    have : (c : ℤ) + 1 = 2 * (b : ℤ) ^ 2 + (d : ℤ) := by exact_mod_cast hd_eq
    linarith
  have hid : (c : ℤ) * ((c : ℤ) + 1) * ((b : ℤ) ^ 2 + b + 1) -
      (b : ℤ) ^ 3 * ((c : ℤ) * b + c + b ^ 2 + b + 1) =
      (b : ℤ) ^ 2 * (2 * (b : ℤ) ^ 4 + (b : ℤ) ^ 3 + 2 * ((b : ℤ) ^ 2 - b - 1)) +
      (d : ℤ) * (3 * (b : ℤ) ^ 4 + 3 * (b : ℤ) ^ 3 + 3 * (b : ℤ) ^ 2 - b - 1) +
      (d : ℤ) ^ 2 * ((b : ℤ) ^ 2 + b + 1) := by
    rw [hcz]
    ring
  have hbz : (3 : ℤ) ≤ b := by exact_mod_cast hb3
  have hdz : (0 : ℤ) ≤ d := Int.natCast_nonneg d
  have ht1 : 0 < (b : ℤ) ^ 2 * (2 * (b : ℤ) ^ 4 + (b : ℤ) ^ 3 + 2 * ((b : ℤ) ^ 2 - b - 1)) := by
    have h1 : 0 < (b : ℤ) ^ 2 := by positivity
    have h2 : 0 < 2 * (b : ℤ) ^ 4 + (b : ℤ) ^ 3 + 2 * ((b : ℤ) ^ 2 - b - 1) := by
      have : 0 ≤ (b : ℤ) ^ 2 - b - 1 := by nlinarith
      nlinarith
    exact mul_pos h1 h2
  have ht2 : 0 ≤ (d : ℤ) * (3 * (b : ℤ) ^ 4 + 3 * (b : ℤ) ^ 3 + 3 * (b : ℤ) ^ 2 - b - 1) := by
    have h2 : 0 ≤ 3 * (b : ℤ) ^ 4 + 3 * (b : ℤ) ^ 3 + 3 * (b : ℤ) ^ 2 - b - 1 := by nlinarith
    exact mul_nonneg hdz h2
  have ht3 : 0 ≤ (d : ℤ) ^ 2 * ((b : ℤ) ^ 2 + b + 1) := by positivity
  linarith

private lemma case_ec1_eb2_not_dvd {b c K i : ℕ} (hb_prime : b.Prime) (hb3 : 3 ≤ b)
    (hc_odd : Odd c) (hsigK : sigma 1 K < 2 * K)
    (hi2 : (c + 1) * i = 2 * b ^ 2 * K)
    (hbi : ¬ b ∣ i)
    (hsig_full : (c + 1) * (b ^ 2 + b + 1) * sigma 1 K = 2 * c * b ^ 2 * K) :
    2 * b ^ 2 ≤ c + 1 ∧ b ^ 3 < 2 * c * K := by
  have hb2_dvd_cp1 : b ^ 2 ∣ c + 1 := by
    have hcop : (b ^ 2).Coprime i := (hb_prime.coprime_iff_not_dvd.mpr hbi).pow_left 2
    exact hcop.dvd_of_dvd_mul_right ⟨2 * K, by rw [hi2]; ring⟩
  have h2_dvd_cp1 : 2 ∣ c + 1 := by
    rcases hc_odd with ⟨kc, rfl⟩
    exact ⟨kc + 1, by ring⟩
  have hb_odd : Odd b := by
    have := hb_prime.eq_two_or_odd
    rw [Nat.odd_iff]
    omega
  have h2b2_dvd_cp1 : 2 * b ^ 2 ∣ c + 1 :=
    nat_coprime_mul_dvd (hb_odd.pow.coprime_two_right.symm) h2_dvd_cp1 hb2_dvd_cp1
  have hge : 2 * b ^ 2 ≤ c + 1 := Nat.le_of_dvd (Nat.succ_pos c) h2b2_dvd_cp1
  have hrem_pos : 1 ≤ 2 * K - sigma 1 K := by omega
  have hid : (c + 1) * (b ^ 2 + b + 1) * (2 * K - sigma 1 K) =
      2 * K * (c * b + c + b ^ 2 + b + 1) := by
    have hle : sigma 1 K ≤ 2 * K := hsigK.le
    zify [hle]
    have hs : ((c : ℤ) + 1) * ((b : ℤ) ^ 2 + b + 1) * sigma 1 K = 2 * c * b ^ 2 * K := by
      exact_mod_cast hsig_full
    linarith
  have hle_K : (c + 1) * (b ^ 2 + b + 1) ≤ 2 * K * (c * b + c + b ^ 2 + b + 1) := by
    calc (c + 1) * (b ^ 2 + b + 1)
        ≤ (c + 1) * (b ^ 2 + b + 1) * (2 * K - sigma 1 K) := Nat.le_mul_of_pos_right _ hrem_pos
      _ = 2 * K * (c * b + c + b ^ 2 + b + 1) := hid
  have hc_pos : 0 < c := by
    have : 9 ≤ b ^ 2 := by nlinarith
    omega
  have hpoly := case_ec1_eb2_not_dvd_poly hb3 hge
  have hmul : b ^ 3 * (c * b + c + b ^ 2 + b + 1) <
      (2 * c * K) * (c * b + c + b ^ 2 + b + 1) := by
    calc b ^ 3 * (c * b + c + b ^ 2 + b + 1)
        < c * ((c + 1) * (b ^ 2 + b + 1)) := by nlinarith
      _ ≤ c * (2 * K * (c * b + c + b ^ 2 + b + 1)) := Nat.mul_le_mul_left c hle_K
      _ = (2 * c * K) * (c * b + c + b ^ 2 + b + 1) := by ring
  exact ⟨hge, Nat.lt_of_mul_lt_mul_right hmul⟩

/-- For any two distinct prime factors `b < c` of an odd perfect number `N`, `b ^ 5 < 2 * N`. -/
theorem prime_pow_five_lt_two_mul_of_lt {N b c : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hbN : b ∈ N.primeFactors) (hcN : c ∈ N.primeFactors) (hbc : b < c) :
    b ^ 5 < 2 * N := by
  have hb_prime := Nat.prime_of_mem_primeFactors hbN
  have hc_prime := Nat.prime_of_mem_primeFactors hcN
  have ⟨hb3, _hbc2⟩ := odd_prime_add_two_le_of_lt ho hbN hcN hbc
  have hb_pos : 0 < b := hb_prime.pos
  have hc_pos : 0 < c := hc_prime.pos
  have heb_pos : 0 < N.factorization b := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hbN)
  have hec_pos : 0 < N.factorization c := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hcN)
  obtain ⟨q, _hq_mem, _hq_mod, _hq_exp_mod, h_even⟩ := euler_exponents ho hN
  by_cases h2bc : 2 ≤ N.factorization b ∧ 2 ≤ N.factorization c
  · let s : Finset ℕ := {b, c}
    have hs_sub : s ⊂ N.primeFactors := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro x hx
        simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · intro heq
        have h4 := four_le_distinct_prime_factor_count ho hN
        have hsc : s.card ≤ 2 := Finset.card_le_two
        rw [heq] at hsc
        omega
    have hcut := rank_cut_product_bound hN ho s hs_sub (Finset.insert_nonempty _ _) (t := b) (by
      intro x hx
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> omega)
    rw [Finset.prod_pair hbc.ne] at hcut
    have hpowb : b ^ 2 ≤ b ^ N.factorization b := Nat.pow_le_pow_right hb_pos h2bc.1
    have hpowc : c ^ 2 ≤ c ^ N.factorization c := Nat.pow_le_pow_right hc_pos h2bc.2
    have hbc2_lt : b ^ 2 < c ^ 2 := Nat.pow_lt_pow_left hbc (by decide)
    have hb2_pos : 0 < b ^ 2 := pow_pos hb_pos 2
    have h5 : 2 * b ^ 5 < 3 * N := by
      calc 2 * b ^ 5 = 2 * b * (b ^ 2 * b ^ 2) := by ring
        _ < 2 * b * (b ^ 2 * c ^ 2) :=
          Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left hbc2_lt hb2_pos) (by positivity)
        _ ≤ 2 * b * (b ^ N.factorization b * c ^ N.factorization c) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hpowb hpowc)
        _ < 3 * N := hcut
    omega
  · by_cases heb1 : N.factorization b = 1
    · have hbq : b = q := by
        by_contra hne
        rcases h_even b hne with ⟨k, hk⟩
        omega
      have hcq : c ≠ q := by rw [← hbq]; exact hbc.ne'
      have hec2 := even_pos_eq_two_or_four_le hec_pos (h_even c hcq)
      have hb5_lt : b ^ 5 < b * c ^ 4 := by
        have hbc4 : b ^ 4 < c ^ 4 := Nat.pow_lt_pow_left hbc (by decide)
        calc b ^ 5 = b * b ^ 4 := by ring
          _ < b * c ^ 4 := Nat.mul_lt_mul_of_pos_left hbc4 hb_pos
      rcases hec2 with hec2 | hec4
      · exact hb5_lt.trans (pair_e1_e2_bound ho hN hbN hcN hbc heb1 hec2)
      · have hdvd : b * c ^ 4 ∣ N := by
          have hb_dvd : b ^ 1 ∣ N := (hb_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr (by omega)
          have hc_dvd : c ^ 4 ∣ N := (hc_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr hec4
          have hcop : (b ^ 1).Coprime (c ^ 4) := ((Nat.coprime_primes hb_prime hc_prime).mpr hbc.ne).pow 1 4
          simpa [pow_one] using nat_coprime_mul_dvd hcop hb_dvd hc_dvd
        have hle := Nat.le_of_dvd hN.2 hdvd
        omega
    · have hec1 : N.factorization c = 1 := by omega
      have hcq : c = q := by
        by_contra hne
        rcases h_even c hne with ⟨k, hk⟩
        omega
      have hbq : b ≠ q := by rw [← hcq]; exact hbc.ne
      have heb2 := even_pos_eq_two_or_four_le heb_pos (h_even b hbq)
      have hb5_lt : b ^ 5 < c * b ^ 4 := by
        calc b ^ 5 = b * b ^ 4 := by ring
          _ < c * b ^ 4 := Nat.mul_lt_mul_of_pos_right hbc (pow_pos hb_pos 4)
      rcases heb2 with heb2 | heb4
      · obtain ⟨K, i, hK1, _hKodd, _hcop_bK, _hcop_cK, hN_eq, hsigK, _hi0, hi1, hi2⟩ :=
          case_ec1_eb2_setup ho hN hbN hcN hbc heb2 hec1
        by_cases hb2i : b ^ 2 ∣ i
        · have hb2_dvd : b ^ 2 ∣ sigma 1 K := by
            have h1 : b ^ 2 ∣ (b ^ 2 + b + 1) * sigma 1 K := by rw [hi1]; exact dvd_mul_of_dvd_right hb2i c
            exact ((odd_coprime_prime_self_sq_add_self_add_one hb_prime).pow_left 2).dvd_of_dvd_mul_left h1
          have hsigK_pos : 0 < sigma 1 K := sigma_pos 1 K (by omega)
          have hb2_lt : b ^ 2 < 2 * K := (Nat.le_of_dvd hsigK_pos hb2_dvd).trans_lt hsigK
          have hcb2_pos : 0 < c * b ^ 2 := Nat.mul_pos hc_pos (pow_pos hb_pos 2)
          calc b ^ 5 < c * b ^ 4 := hb5_lt
            _ = (c * b ^ 2) * b ^ 2 := by ring
            _ < (c * b ^ 2) * (2 * K) := Nat.mul_lt_mul_of_pos_left hb2_lt hcb2_pos
            _ = 2 * N := by rw [hN_eq]; ring
        · by_cases hbi : b ∣ i
          · have hbc_lt := case_ec1_eb2_mid_dvd hb_prime hc_prime
              (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hbN))
              (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hcN))
              hK1 hsigK hi1 hi2 hbi hb2i
            have hbc2_lt : b ^ 2 < c ^ 2 := Nat.pow_lt_pow_left hbc (by decide)
            have hb3_pos : 0 < b ^ 3 := pow_pos hb_pos 3
            have hcb2_pos : 0 < c * b ^ 2 := Nat.mul_pos hc_pos (pow_pos hb_pos 2)
            calc b ^ 5 = b ^ 3 * b ^ 2 := by ring
              _ < b ^ 3 * c ^ 2 := Nat.mul_lt_mul_of_pos_left hbc2_lt hb3_pos
              _ = (c * b ^ 2) * (b * c) := by ring
              _ < (c * b ^ 2) * (2 * K) := Nat.mul_lt_mul_of_pos_left hbc_lt hcb2_pos
              _ = 2 * N := by rw [hN_eq]; ring
          · have hsig_full : (c + 1) * (b ^ 2 + b + 1) * sigma 1 K = 2 * c * b ^ 2 * K := by
              calc (c + 1) * (b ^ 2 + b + 1) * sigma 1 K
                  = (c + 1) * ((b ^ 2 + b + 1) * sigma 1 K) := by ring
                _ = (c + 1) * (c * i) := by rw [hi1]
                _ = c * ((c + 1) * i) := by ring
                _ = 2 * c * b ^ 2 * K := by rw [hi2]; ring
            have ⟨_hge, hb3_lt⟩ := case_ec1_eb2_not_dvd hb_prime hb3
              (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hcN))
              hsigK hi2 hbi hsig_full
            have hb2_pos : 0 < b ^ 2 := pow_pos hb_pos 2
            calc b ^ 5 = b ^ 2 * b ^ 3 := by ring
              _ < b ^ 2 * (2 * c * K) := Nat.mul_lt_mul_of_pos_left hb3_lt hb2_pos
              _ = 2 * N := by rw [hN_eq]; ring
      · have hdvd : c * b ^ 4 ∣ N := by
          have hc_dvd : c ^ 1 ∣ N := (hc_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr (by omega)
          have hb_dvd : b ^ 4 ∣ N := (hb_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr heb4
          have hcop : (c ^ 1).Coprime (b ^ 4) := ((Nat.coprime_primes hc_prime hb_prime).mpr hbc.ne').pow 1 4
          simpa [pow_one] using nat_coprime_mul_dvd hcop hc_dvd hb_dvd
        have hle := Nat.le_of_dvd hN.2 hdvd
        omega

private lemma triple_ec1_eb2_mid_dvd {N a b c K i : ℕ} (ho : Odd N) (hN : N.Perfect)
    (haN : a ∈ N.primeFactors) (hbN : b ∈ N.primeFactors) (hcN : c ∈ N.primeFactors)
    (hab : a < b) (hbc : b < c) (heb2 : N.factorization b = 2) (hec1 : N.factorization c = 1)
    (hK1 : 1 < K) (hN_eq : N = c * b ^ 2 * K) (hsigK : sigma 1 K < 2 * K)
    (hi1 : (b ^ 2 + b + 1) * sigma 1 K = c * i) (hi2 : (c + 1) * i = 2 * b ^ 2 * K)
    (hbi : b ∣ i) (hb2i : ¬ b ^ 2 ∣ i) :
    (a * b * c) ^ 5 < (2 * N) ^ 3 := by
  have ha_prime := Nat.prime_of_mem_primeFactors haN
  have hb_prime := Nat.prime_of_mem_primeFactors hbN
  have hc_prime := Nat.prime_of_mem_primeFactors hcN
  have ha_pos : 0 < a := ha_prime.pos
  have hb_pos : 0 < b := hb_prime.pos
  have hc_pos : 0 < c := hc_prime.pos
  have hac : a < c := hab.trans hbc
  have hbc_lt := case_ec1_eb2_mid_dvd hb_prime hc_prime
    (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hbN))
    (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hcN))
    hK1 hsigK hi1 hi2 hbi hb2i
  have hcb2_pos : 0 < c * b ^ 2 := Nat.mul_pos hc_pos (pow_pos hb_pos 2)
  have hc2b3_lt : c ^ 2 * b ^ 3 < 2 * N := by
    calc c ^ 2 * b ^ 3 = (c * b ^ 2) * (b * c) := by ring
      _ < (c * b ^ 2) * (2 * K) := Nat.mul_lt_mul_of_pos_left hbc_lt hcb2_pos
      _ = 2 * N := by rw [hN_eq]; ring
  have hc3_lt : c ^ 3 < 3 * N := prime_cube_lt_three_mul hN ho hcN
  have ha3_lt : 2 * a ^ 3 * b ^ 2 * c < 3 * N := by
    let s3 : Finset ℕ := {a, b, c}
    have hs3_sub : s3 ⊂ N.primeFactors := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro x hx
        simp only [s3, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · intro heq
        have h4 := four_le_distinct_prime_factor_count ho hN
        have hsc : s3.card ≤ 3 := Finset.card_le_three
        rw [heq] at hsc
        omega
    have hcut := rank_cut_product_bound hN ho s3 hs3_sub (Finset.insert_nonempty _ _) (t := a) (by
      intro x hx
      simp only [s3, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> omega)
    have hprod3 : (∏ x ∈ s3, x ^ N.factorization x) = a ^ N.factorization a * b ^ 2 * c := by
      have ha_nmem : a ∉ ({b, c} : Finset ℕ) := by simp [hab.ne, hac.ne]
      rw [Finset.prod_insert ha_nmem, Finset.prod_pair hbc.ne, heb2, hec1, pow_one]
      ring
    rw [hprod3] at hcut
    have hea_pos : 0 < N.factorization a := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp haN)
    have hea2 : 2 ≤ N.factorization a := by
      obtain ⟨q, _hq_mem, _hq_mod, _hq_exp_mod, h_even⟩ := euler_exponents ho hN
      have hcq : c = q := by
        by_contra hne
        rcases h_even c hne with ⟨k, hk⟩
        omega
      have haq : a ≠ q := by rw [← hcq]; exact hac.ne
      rcases h_even a haq with ⟨k, hk⟩
      omega
    have ha2_le : a ^ 2 ≤ a ^ N.factorization a := Nat.pow_le_pow_right ha_pos hea2
    calc 2 * a ^ 3 * b ^ 2 * c = 2 * a * (a ^ 2 * b ^ 2 * c) := by ring
      _ ≤ 2 * a * (a ^ N.factorization a * b ^ 2 * c) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ha2_le))
      _ < 3 * N := hcut
  have hbig_lhs : 2 ^ 45 * ((a * b * c) ^ 5) ^ 27 =
      (2 * a ^ 3 * b ^ 2 * c) ^ 45 * (c ^ 2 * b ^ 3) ^ 15 * (c ^ 3) ^ 20 := by ring
  have hbig_lt : (2 * a ^ 3 * b ^ 2 * c) ^ 45 * (c ^ 2 * b ^ 3) ^ 15 * (c ^ 3) ^ 20 <
      (3 * N) ^ 45 * (2 * N) ^ 15 * (3 * N) ^ 20 := by
    have h1 := Nat.pow_lt_pow_left ha3_lt (by decide : 45 ≠ 0)
    have h2 := Nat.pow_lt_pow_left hc2b3_lt (by decide : 15 ≠ 0)
    have h3 := Nat.pow_lt_pow_left hc3_lt (by decide : 20 ≠ 0)
    exact Nat.mul_lt_mul'' (Nat.mul_lt_mul'' h1 h2) h3
  have hconst : 3 ^ 65 * 2 ^ 15 < 2 ^ 45 * 2 ^ 81 := by decide
  have hN1 : 1 ≤ N := hN.2
  have hN80 : N ^ 80 ≤ N ^ 81 := Nat.pow_le_pow_right hN1 (by decide)
  have hbig_rhs : (3 * N) ^ 45 * (2 * N) ^ 15 * (3 * N) ^ 20 <
      2 ^ 45 * ((2 * N) ^ 3) ^ 27 := by
    calc (3 * N) ^ 45 * (2 * N) ^ 15 * (3 * N) ^ 20
        = (3 ^ 65 * 2 ^ 15) * N ^ 80 := by ring
      _ ≤ (3 ^ 65 * 2 ^ 15) * N ^ 81 := Nat.mul_le_mul_left _ hN80
      _ < (2 ^ 45 * 2 ^ 81) * N ^ 81 := Nat.mul_lt_mul_of_pos_right hconst (pow_pos hN.2 81)
      _ = 2 ^ 45 * ((2 * N) ^ 3) ^ 27 := by ring
  have hpow_lt : 2 ^ 45 * ((a * b * c) ^ 5) ^ 27 < 2 ^ 45 * ((2 * N) ^ 3) ^ 27 :=
    hbig_lhs ▸ hbig_lt.trans hbig_rhs
  exact lt_of_pow_lt_pow_left' 27 (Nat.lt_of_mul_lt_mul_left hpow_lt)

private lemma two_mul_lt_three_mul_of_odd_sigma_dvd {b L : ℕ} (hb_prime : b.Prime)
    (hL1 : 1 < L) (hLodd : Odd L) (hsigL_odd : Odd (sigma 1 L))
    (hsigL : sigma 1 L < 2 * L) (hb_dvd_sigL : b ∣ sigma 1 L) :
    2 * b < 3 * L := by
  have hL_pos : 0 < L := by omega
  have hsigL_pos : 0 < sigma 1 L := sigma_pos 1 L hL_pos.ne'
  rcases eq_or_lt_of_le (Nat.le_of_dvd hsigL_pos hb_dvd_sigL) with hbeq | hblt
  · obtain ⟨p, hpL⟩ := Nat.nonempty_primeFactors.mpr hL1
    have hp_prime := Nat.prime_of_mem_primeFactors hpL
    have hp_dvd_L : p ∣ L := Nat.dvd_of_mem_primeFactors hpL
    have hp_odd : Odd p := hLodd.of_dvd_nat hp_dvd_L
    have hp3 : 3 ≤ p := by
      have := hp_prime.two_le; have := hp_odd.not_two_dvd_nat; omega
    have hpe_pos : 0 < L.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hpL)
    have hp_pow_gt1 : 1 < p ^ L.factorization p := one_lt_pow₀ hp_prime.one_lt hpe_pos.ne'
    have hsigp_gt1 : 1 < sigma 1 (p ^ L.factorization p) :=
      hp_pow_gt1.trans (self_lt_sigma_of_one_lt hp_pow_gt1)
    have hsigp_dvd : sigma 1 (p ^ L.factorization p) ∣ sigma 1 L := by
      have hord := (Nat.ordProj_mul_ordCompl_eq_self L p).symm
      have hcop_ord : (p ^ L.factorization p).Coprime (ordCompl[p] L) :=
        (Nat.coprime_ordCompl hp_prime hL_pos.ne').pow_left _
      have hsigL_mul : sigma 1 L = sigma 1 (p ^ L.factorization p) * sigma 1 (ordCompl[p] L) := by
        conv_lhs => rw [hord]
        exact isMultiplicative_sigma.map_mul_of_coprime hcop_ord
      exact ⟨sigma 1 (ordCompl[p] L), hsigL_mul⟩
    rw [← hbeq] at hsigp_dvd
    have hsigp_eq : sigma 1 (p ^ L.factorization p) = b :=
      (hb_prime.eq_one_or_self_of_dvd _ hsigp_dvd).resolve_left hsigp_gt1.ne'
    have hlocal := two_mul_sigma_prime_pow_lt_three_mul hp_prime hp3 (L.factorization p)
    rw [hsigp_eq] at hlocal
    have hpe_le : p ^ L.factorization p ≤ L :=
      Nat.le_of_dvd hL_pos (Nat.ordProj_dvd L p)
    calc 2 * b < 3 * p ^ L.factorization p := hlocal
      _ ≤ 3 * L := Nat.mul_le_mul_left 3 hpe_le
  · obtain ⟨m, hm⟩ := hb_dvd_sigL
    have hm_odd : Odd m := hsigL_odd.of_dvd_nat ⟨b, by rw [hm, mul_comm]⟩
    have hm3 : 3 ≤ m := by
      rcases hm_odd with ⟨km, hkm⟩
      have hm1 : m ≠ 1 := by
        intro h1
        rw [h1, mul_one] at hm
        omega
      omega
    have h3b_le : 3 * b ≤ sigma 1 L := by
      calc 3 * b ≤ m * b := Nat.mul_le_mul_right b hm3
        _ = b * m := mul_comm m b
        _ = sigma 1 L := hm.symm
    have h2b_lt_3b : 2 * b < 3 * b := Nat.mul_lt_mul_of_pos_right (by decide) hb_prime.pos
    have h2L_lt_3L : 2 * L < 3 * L := Nat.mul_lt_mul_of_pos_right (by decide) hL_pos
    exact ((h2b_lt_3b.trans_le h3b_le).trans hsigL).trans h2L_lt_3L

private lemma triple_ec1_eb2_ea2 {N a b c K i : ℕ} (ho : Odd N) (hN : N.Perfect)
    (haN : a ∈ N.primeFactors) (hbN : b ∈ N.primeFactors) (hcN : c ∈ N.primeFactors)
    (hab : a < b) (hbc : b < c) (hq_eq : c ∈ N.primeFactors)
    (hea2 : N.factorization a = 2) (heb2 : N.factorization b = 2) (hec1 : N.factorization c = 1)
    (h_even : ∀ q_1, q_1 ≠ c → Even (N.factorization q_1))
    (_hK1 : 1 < K) (hN_eq : N = c * b ^ 2 * K) (hsigK : sigma 1 K < 2 * K)
    (hi1 : (b ^ 2 + b + 1) * sigma 1 K = c * i) (hi2 : (c + 1) * i = 2 * b ^ 2 * K)
    (hmid : ¬ (b ∣ i ∧ ¬ b ^ 2 ∣ i)) :
    (a * b * c) ^ 5 < (2 * N) ^ 3 := by
  have ha_prime := Nat.prime_of_mem_primeFactors haN
  have hb_prime := Nat.prime_of_mem_primeFactors hbN
  have hc_prime := Nat.prime_of_mem_primeFactors hcN
  have ha_pos : 0 < a := ha_prime.pos
  have hb_pos : 0 < b := hb_prime.pos
  have hc_pos : 0 < c := hc_prime.pos
  have hac : a < c := hab.trans hbc
  have ⟨ha3, hab2⟩ := odd_prime_add_two_le_of_lt ho haN hbN hab
  have ⟨hb3, _hbc2⟩ := odd_prime_add_two_le_of_lt ho hbN hcN hbc
  have hc3_lt : c ^ 3 < 3 * N := prime_cube_lt_three_mul hN ho hcN
  let s3 : Finset ℕ := {a, b, c}
  have hs3_sub : s3 ⊆ N.primeFactors := by
    intro x hx
    simp only [s3, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hs3_card : s3.card < N.primeFactors.card := by
    have h4 := four_le_distinct_prime_factor_count ho hN
    have hsc : s3.card ≤ 3 := Finset.card_le_three
    omega
  obtain ⟨hLprod, hLcop, hL1, hLodd, _hsigL_A, hsigL, hsigL_eq⟩ :=
    primeFactors_sdiff_decomp ho hN s3 hs3_sub (Finset.insert_nonempty _ _) hs3_card
  set L := ∏ p ∈ N.primeFactors \ s3, p ^ N.factorization p
  have hA3_eq : (∏ p ∈ s3, p ^ N.factorization p) = a ^ 2 * b ^ 2 * c := by
    have ha_nmem : a ∉ ({b, c} : Finset ℕ) := by simp [hab.ne, hac.ne]
    rw [Finset.prod_insert ha_nmem, Finset.prod_pair hbc.ne, hea2, heb2, hec1, pow_one]
    ring
  have hsigA3_eq : (∏ p ∈ s3, sigma 1 (p ^ N.factorization p)) =
      (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c + 1) := by
    have ha_nmem : a ∉ ({b, c} : Finset ℕ) := by simp [hab.ne, hac.ne]
    rw [Finset.prod_insert ha_nmem, Finset.prod_pair hbc.ne, hea2, heb2, hec1,
      sigma_one_apply_prime_pow ha_prime, sigma_one_apply_prime_pow hb_prime,
      sigma_one_apply_prime_pow hc_prime]
    simp [Finset.sum_range_succ]
    ring
  rw [hA3_eq] at hLprod
  rw [hA3_eq] at hLcop
  rw [hsigA3_eq] at hsigL_eq
  have hK_eq : K = a ^ 2 * L := by
    apply Nat.mul_left_cancel (Nat.mul_pos hc_pos (pow_pos hb_pos 2))
    calc c * b ^ 2 * K = N := hN_eq.symm
      _ = c * b ^ 2 * (a ^ 2 * L) := by rw [hLprod]; ring
  have ha_cop_L : a.Coprime L := Nat.Coprime.coprime_dvd_left ⟨a * b ^ 2 * c, by ring⟩ hLcop
  have hL_sq : IsSquare L := by
    apply Nat.isSquare_iff_even_factorization.mpr
    intro r _
    by_cases hrL : r ∈ L.primeFactors
    · have hr_dvd_L : r ∣ L := Nat.dvd_of_mem_primeFactors hrL
      have hr_prime := Nat.prime_of_mem_primeFactors hrL
      have hr_ne_c : r ≠ c := by
        intro rfl
        have hcL : r.Coprime L := Nat.Coprime.coprime_dvd_left (dvd_mul_left r (a ^ 2 * b ^ 2)) hLcop
        have hr1 : r = 1 := by simpa using hcL.coprime_dvd_right hr_dvd_L
        exact hr_prime.ne_one hr1
      have hL_dvd_cof : N.factorization r = L.factorization r := by
        have hN_fac : N.factorization r = (a ^ 2 * b ^ 2 * c).factorization r + L.factorization r := by
          have habc2_ne : a ^ 2 * b ^ 2 * c ≠ 0 :=
            Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero 2 ha_prime.ne_zero) (pow_ne_zero 2 hb_prime.ne_zero)) hc_prime.ne_zero
          rw [← Finsupp.add_apply, ← Nat.factorization_mul habc2_ne (by omega), ← hLprod]
        have h0 : (a ^ 2 * b ^ 2 * c).factorization r = 0 := by
          apply Nat.factorization_eq_zero_of_not_dvd
          intro hd
          have hr1 : r = 1 := by simpa using (hLcop.coprime_dvd_left hd).coprime_dvd_right hr_dvd_L
          exact hr_prime.ne_one hr1
        omega
      rw [← hL_dvd_cof]
      exact h_even r hr_ne_c
    · rw [Finsupp.notMem_support_iff.mp hrL]
      exact Even.zero
  have hsigL_odd : Odd (sigma 1 L) := (odd_sigma_iff_square_of_odd hLodd).mpr hL_sq
  have hL_pos : 0 < L := by omega
  have hsigL_pos : 0 < sigma 1 L := sigma_pos 1 L hL_pos.ne'
  by_cases hb2i : b ^ 2 ∣ i
  · have hb2_dvd_sigK : b ^ 2 ∣ sigma 1 K := by
      have h1 : b ^ 2 ∣ (b ^ 2 + b + 1) * sigma 1 K := by rw [hi1]; exact dvd_mul_of_dvd_right hb2i c
      exact ((odd_coprime_prime_self_sq_add_self_add_one hb_prime).pow_left 2).dvd_of_dvd_mul_left h1
    have hsigK_eq : sigma 1 K = (a ^ 2 + a + 1) * sigma 1 L := by
      rw [hK_eq, isMultiplicative_sigma.map_mul_of_coprime (ha_cop_L.pow_left 2),
        sigma_one_apply_prime_pow ha_prime]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
      ring
    rw [hsigK_eq] at hb2_dvd_sigK
    have hb_dvd_sigL : b ∣ sigma 1 L := by
      by_contra hnd
      have hcop : (b ^ 2).Coprime (sigma 1 L) := (hb_prime.coprime_iff_not_dvd.mpr hnd).pow_left 2
      have hdvd_a : b ^ 2 ∣ a ^ 2 + a + 1 := hcop.dvd_of_dvd_mul_right hb2_dvd_sigK
      have hle := Nat.le_of_dvd (by positivity) hdvd_a
      have hlt : a ^ 2 + a + 1 < b ^ 2 := by nlinarith
      omega
    have h2b_lt_3L : 2 * b < 3 * L :=
      two_mul_lt_three_mul_of_odd_sigma_dvd hb_prime hL1 hLodd hsigL_odd hsigL hb_dvd_sigL
    have h4b2 : 4 * b ^ 2 < 9 * L ^ 2 := by
      calc 4 * b ^ 2 = (2 * b) ^ 2 := by ring
        _ < (3 * L) ^ 2 := Nat.pow_lt_pow_left h2b_lt_3L (by decide)
        _ = 9 * L ^ 2 := by ring
    have h3b2_lt : 3 * b ^ 2 < 8 * L ^ 2 := by
      have h1 : 4 * (3 * b ^ 2) < 4 * (8 * L ^ 2) := by
        calc 4 * (3 * b ^ 2) = 3 * (4 * b ^ 2) := by ring
          _ < 3 * (9 * L ^ 2) := Nat.mul_lt_mul_of_pos_left h4b2 (by decide)
          _ = 27 * L ^ 2 := by ring
          _ ≤ 32 * L ^ 2 := Nat.mul_le_mul_right (L ^ 2) (by decide)
          _ = 4 * (8 * L ^ 2) := by ring
      exact Nat.lt_of_mul_lt_mul_left h1
    have h3ab_lt : 3 * a * b < 8 * L ^ 2 := by
      have h1 : 3 * a * b < 3 * b ^ 2 := by
        calc 3 * a * b = (3 * b) * a := by ring
          _ < (3 * b) * b := Nat.mul_lt_mul_of_pos_left hab (Nat.mul_pos (by decide) hb_pos)
          _ = 3 * b ^ 2 := by ring
      exact h1.trans h3b2_lt
    have hc2_lt : c ^ 2 < 8 * a * b * L ^ 3 := by
      have hc2_lt1 : c ^ 2 < 3 * a ^ 2 * b ^ 2 * L := by
        apply Nat.lt_of_mul_lt_mul_left (a := c)
        calc c * c ^ 2 = c ^ 3 := by ring
          _ < 3 * N := hc3_lt
          _ = c * (3 * a ^ 2 * b ^ 2 * L) := by rw [hLprod]; ring
      have hab_pos : 0 < a * b := Nat.mul_pos ha_pos hb_pos
      calc c ^ 2 < 3 * a ^ 2 * b ^ 2 * L := hc2_lt1
        _ = (a * b * L) * (3 * a * b) := by ring
        _ < (a * b * L) * (8 * L ^ 2) := Nat.mul_lt_mul_of_pos_left h3ab_lt (Nat.mul_pos hab_pos hL_pos)
        _ = 8 * a * b * L ^ 3 := by ring
    have ha5b5c3_pos : 0 < a ^ 5 * b ^ 5 * c ^ 3 :=
      Nat.mul_pos (Nat.mul_pos (pow_pos ha_pos 5) (pow_pos hb_pos 5)) (pow_pos hc_pos 3)
    calc (a * b * c) ^ 5 = a ^ 5 * b ^ 5 * c ^ 3 * c ^ 2 := by ring
      _ < a ^ 5 * b ^ 5 * c ^ 3 * (8 * a * b * L ^ 3) :=
        Nat.mul_lt_mul_of_pos_left hc2_lt ha5b5c3_pos
      _ = (2 * (a ^ 2 * b ^ 2 * c * L)) ^ 3 := by ring
      _ = (2 * N) ^ 3 := by rw [hLprod]
  · have hbi : ¬ b ∣ i := fun h => hmid ⟨h, hb2i⟩
    have hsig_full : (c + 1) * (b ^ 2 + b + 1) * sigma 1 K = 2 * c * b ^ 2 * K := by
      calc (c + 1) * (b ^ 2 + b + 1) * sigma 1 K
          = (c + 1) * ((b ^ 2 + b + 1) * sigma 1 K) := by ring
        _ = (c + 1) * (c * i) := by rw [hi1]
        _ = c * ((c + 1) * i) := by ring
        _ = 2 * c * b ^ 2 * K := by rw [hi2]; ring
    have ⟨hge, _⟩ := case_ec1_eb2_not_dvd hb_prime hb3
      (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hcN))
      hsigK hi2 hbi hsig_full
    have hb5 : 5 ≤ b := by omega
    have hc_gt_b : b ^ 2 + b + 1 < c := by nlinarith only [hb5, hge]
    have hc_gt_a : a ^ 2 + a + 1 < c := by nlinarith only [hab, hb5, hc_gt_b]
    have hc_dvd_L : c ∣ sigma 1 L := by
      have hc_dvd_prod : c ∣ (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * sigma 1 L := by
        have hdvd1 : c ∣ (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c + 1) * sigma 1 L := by
          rw [show (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c + 1) * sigma 1 L = 2 * N from hsigL_eq,
            hLprod]
          exact ⟨2 * a ^ 2 * b ^ 2 * L, by ring⟩
        have hc_cop_cp1 : c.Coprime (c + 1) := by
          apply hc_prime.coprime_iff_not_dvd.mpr
          intro hd
          exact hc_prime.not_dvd_one ((Nat.dvd_add_right (dvd_refl c)).mp hd)
        exact hc_cop_cp1.dvd_of_dvd_mul_right (by simpa [mul_assoc, mul_left_comm, mul_comm] using hdvd1)
      have hca : c.Coprime (a ^ 2 + a + 1) :=
        hc_prime.coprime_iff_not_dvd.mpr fun hd =>
          by have := Nat.le_of_dvd (by positivity) hd; omega
      have hcb : c.Coprime (b ^ 2 + b + 1) :=
        hc_prime.coprime_iff_not_dvd.mpr fun hd =>
          by have := Nat.le_of_dvd (by positivity) hd; omega
      exact (hca.mul_right hcb).dvd_of_dvd_mul_left hc_dvd_prod
    have hc_lt_2L : c < 2 * L := (Nat.le_of_dvd hsigL_pos hc_dvd_L).trans_lt hsigL
    have habc_gt1 : 1 < a * b * c := by
      calc 1 < a := ha_prime.one_lt
        _ < a * b := lt_mul_of_one_lt_right ha_pos hb_prime.one_lt
        _ < a * b * c := lt_mul_of_one_lt_right (Nat.mul_pos ha_pos hb_pos) hc_prime.one_lt
    have ha6b6c3_pos : 0 < a ^ 6 * b ^ 6 * c ^ 3 :=
      Nat.mul_pos (Nat.mul_pos (pow_pos ha_pos 6) (pow_pos hb_pos 6)) (pow_pos hc_pos 3)
    calc (a * b * c) ^ 5 < (a * b * c) ^ 6 := Nat.pow_lt_pow_right habc_gt1 (by decide)
      _ = a ^ 6 * b ^ 6 * c ^ 3 * c ^ 3 := by ring
      _ < a ^ 6 * b ^ 6 * c ^ 3 * (2 * L) ^ 3 :=
        Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hc_lt_2L (by decide)) ha6b6c3_pos
      _ = (2 * (a ^ 2 * b ^ 2 * c * L)) ^ 3 := by ring
      _ = (2 * N) ^ 3 := by rw [hLprod]

private lemma triple_ec1_eb2_not_mid {N a b c K i : ℕ} (ho : Odd N) (hN : N.Perfect)
    (haN : a ∈ N.primeFactors) (hbN : b ∈ N.primeFactors) (hcN : c ∈ N.primeFactors)
    (hab : a < b) (hbc : b < c) (heb2 : N.factorization b = 2) (hec1 : N.factorization c = 1)
    (h_even : ∀ q_1, q_1 ≠ c → Even (N.factorization q_1))
    (hK1 : 1 < K) (hN_eq : N = c * b ^ 2 * K) (hsigK : sigma 1 K < 2 * K)
    (hi1 : (b ^ 2 + b + 1) * sigma 1 K = c * i) (hi2 : (c + 1) * i = 2 * b ^ 2 * K)
    (hmid : ¬ (b ∣ i ∧ ¬ b ^ 2 ∣ i)) :
    (a * b * c) ^ 5 < (2 * N) ^ 3 := by
  have ha_prime := Nat.prime_of_mem_primeFactors haN
  have hb_prime := Nat.prime_of_mem_primeFactors hbN
  have hc_prime := Nat.prime_of_mem_primeFactors hcN
  have ha_pos : 0 < a := ha_prime.pos
  have hb_pos : 0 < b := hb_prime.pos
  have hc_pos : 0 < c := hc_prime.pos
  have hac : a < c := hab.trans hbc
  have ⟨_ha3, hab2⟩ := odd_prime_add_two_le_of_lt ho haN hbN hab
  have ⟨hb3, _hbc2⟩ := odd_prime_add_two_le_of_lt ho hbN hcN hbc
  have hea_pos : 0 < N.factorization a := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp haN)
  have hea2 := even_pos_eq_two_or_four_le hea_pos (h_even a hac.ne)
  rcases hea2 with hea2 | hea4
  · exact triple_ec1_eb2_ea2 ho hN haN hbN hcN hab hbc hcN hea2 heb2 hec1 h_even hK1 hN_eq hsigK hi1 hi2 hmid
  · have hc3_lt : c ^ 3 < 3 * N := prime_cube_lt_three_mul hN ho hcN
    have hb4c_lt : b ^ 4 * c < 2 * N := by
      by_cases hb2i : b ^ 2 ∣ i
      · have hb2_dvd : b ^ 2 ∣ sigma 1 K := by
          have h1 : b ^ 2 ∣ (b ^ 2 + b + 1) * sigma 1 K := by rw [hi1]; exact dvd_mul_of_dvd_right hb2i c
          exact ((odd_coprime_prime_self_sq_add_self_add_one hb_prime).pow_left 2).dvd_of_dvd_mul_left h1
        have hsigK_pos : 0 < sigma 1 K := sigma_pos 1 K (by omega)
        have hb2_lt : b ^ 2 < 2 * K := (Nat.le_of_dvd hsigK_pos hb2_dvd).trans_lt hsigK
        have hcb2_pos : 0 < c * b ^ 2 := Nat.mul_pos hc_pos (pow_pos hb_pos 2)
        calc b ^ 4 * c = (c * b ^ 2) * b ^ 2 := by ring
          _ < (c * b ^ 2) * (2 * K) := Nat.mul_lt_mul_of_pos_left hb2_lt hcb2_pos
          _ = 2 * N := by rw [hN_eq]; ring
      · have hbi : ¬ b ∣ i := fun h => hmid ⟨h, hb2i⟩
        have hsig_full : (c + 1) * (b ^ 2 + b + 1) * sigma 1 K = 2 * c * b ^ 2 * K := by
          calc (c + 1) * (b ^ 2 + b + 1) * sigma 1 K
              = (c + 1) * ((b ^ 2 + b + 1) * sigma 1 K) := by ring
            _ = (c + 1) * (c * i) := by rw [hi1]
            _ = c * ((c + 1) * i) := by ring
            _ = 2 * c * b ^ 2 * K := by rw [hi2]; ring
        have ⟨hge, _⟩ := case_ec1_eb2_not_dvd hb_prime hb3
          (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hcN))
          hsigK hi2 hbi hsig_full
        have hb5 : 5 ≤ b := by omega
        have hc2_ge : 3 * b ^ 4 ≤ c ^ 2 := by
          have h1 : 2 * b ^ 2 - 1 ≤ c := by omega
          have h2 : 3 * b ^ 4 ≤ (2 * b ^ 2 - 1) ^ 2 := by
            obtain ⟨k, hk⟩ : ∃ k, b = k + 5 := ⟨b - 5, by omega⟩
            zify [show 1 ≤ 2 * b ^ 2 by nlinarith]
            have hbz : (b : ℤ) = (k : ℤ) + 5 := by exact_mod_cast hk
            rw [hbz]
            nlinarith [sq_nonneg (k : ℤ), Int.natCast_nonneg k]
          exact h2.trans (Nat.pow_le_pow_left h1 2)
        have hc2_lt : c ^ 2 < 3 * b ^ 2 * K := by
          apply Nat.lt_of_mul_lt_mul_left (a := c)
          calc c * c ^ 2 = c ^ 3 := by ring
            _ < 3 * N := hc3_lt
            _ = c * (3 * b ^ 2 * K) := by rw [hN_eq]; ring
        have hb2_lt_K : b ^ 2 < K := by nlinarith
        have hcb2_pos : 0 < c * b ^ 2 := Nat.mul_pos hc_pos (pow_pos hb_pos 2)
        calc b ^ 4 * c = (c * b ^ 2) * b ^ 2 := by ring
          _ < (c * b ^ 2) * K := Nat.mul_lt_mul_of_pos_left hb2_lt_K hcb2_pos
          _ = N := by rw [hN_eq]
          _ < 2 * N := by omega
    have hcop_ab : a.Coprime b := (Nat.coprime_primes ha_prime hb_prime).mpr hab.ne
    have hcop_ac : a.Coprime c := (Nat.coprime_primes ha_prime hc_prime).mpr hac.ne
    have hcop_bc : b.Coprime c := (Nat.coprime_primes hb_prime hc_prime).mpr hbc.ne
    have hdvd : a ^ 4 * b ^ 2 * c ∣ N := by
      have ha_dvd := (ha_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr hea4
      have hb_dvd := (hb_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr heb2.ge
      have hc_dvd : c ^ 1 ∣ N := (hc_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr hec1.ge
      have h1 : a ^ 4 * b ^ 2 ∣ N := nat_coprime_mul_dvd (hcop_ab.pow 4 2) ha_dvd hb_dvd
      have hcop_ab_c : (a ^ 4 * b ^ 2).Coprime (c ^ 1) :=
        (hcop_ac.pow 4 1).mul_left (hcop_bc.pow 2 1)
      simpa [pow_one] using nat_coprime_mul_dvd hcop_ab_c h1 hc_dvd
    have ha4_le : a ^ 4 * b ^ 2 * c ≤ N := Nat.le_of_dvd hN.2 hdvd
    have hbig_lhs : ((a * b * c) ^ 5) ^ 24 =
        (a ^ 4 * b ^ 2 * c) ^ 30 * (b ^ 4 * c) ^ 15 * (c ^ 3) ^ 25 := by ring
    have hbig_lt : (a ^ 4 * b ^ 2 * c) ^ 30 * (b ^ 4 * c) ^ 15 * (c ^ 3) ^ 25 <
        N ^ 30 * (2 * N) ^ 15 * (3 * N) ^ 25 := by
      have h1 : (a ^ 4 * b ^ 2 * c) ^ 30 ≤ N ^ 30 := Nat.pow_le_pow_left ha4_le 30
      have h2 := Nat.pow_lt_pow_left hb4c_lt (by decide : 15 ≠ 0)
      have h3 := Nat.pow_lt_pow_left hc3_lt (by decide : 25 ≠ 0)
      have h12 : (a ^ 4 * b ^ 2 * c) ^ 30 * (b ^ 4 * c) ^ 15 < N ^ 30 * (2 * N) ^ 15 := by
        calc (a ^ 4 * b ^ 2 * c) ^ 30 * (b ^ 4 * c) ^ 15
            ≤ N ^ 30 * (b ^ 4 * c) ^ 15 := Nat.mul_le_mul_right _ h1
          _ < N ^ 30 * (2 * N) ^ 15 := Nat.mul_lt_mul_of_pos_left h2 (pow_pos hN.2 30)
      exact Nat.mul_lt_mul'' h12 h3
    have hconst : 2 ^ 15 * 3 ^ 25 < 2 ^ 72 := by decide
    have hN1 : 1 ≤ N := hN.2
    have hN70 : N ^ 70 ≤ N ^ 72 := Nat.pow_le_pow_right hN1 (by decide)
    have hbig_rhs : N ^ 30 * (2 * N) ^ 15 * (3 * N) ^ 25 < ((2 * N) ^ 3) ^ 24 := by
      calc N ^ 30 * (2 * N) ^ 15 * (3 * N) ^ 25
          = (2 ^ 15 * 3 ^ 25) * N ^ 70 := by ring
        _ ≤ (2 ^ 15 * 3 ^ 25) * N ^ 72 := Nat.mul_le_mul_left _ hN70
        _ < 2 ^ 72 * N ^ 72 := Nat.mul_lt_mul_of_pos_right hconst (pow_pos hN.2 72)
        _ = ((2 * N) ^ 3) ^ 24 := by ring
    exact lt_of_pow_lt_pow_left' 24 (hbig_lhs ▸ hbig_lt.trans hbig_rhs)

/-- For any three distinct prime factors `a < b < c` of an odd perfect number `N`,
`(a * b * c) ^ 5 < (2 * N) ^ 3`. -/
theorem prime_triple_prod_pow_five_lt {N a b c : ℕ} (ho : Odd N) (hN : N.Perfect)
    (haN : a ∈ N.primeFactors) (hbN : b ∈ N.primeFactors) (hcN : c ∈ N.primeFactors)
    (hab : a < b) (hbc : b < c) :
    (a * b * c) ^ 5 < (2 * N) ^ 3 := by
  have ha_prime := Nat.prime_of_mem_primeFactors haN
  have hb_prime := Nat.prime_of_mem_primeFactors hbN
  have hc_prime := Nat.prime_of_mem_primeFactors hcN
  have hac : a < c := hab.trans hbc
  have ha_pos : 0 < a := ha_prime.pos
  have hb_pos : 0 < b := hb_prime.pos
  have hc_pos : 0 < c := hc_prime.pos
  have hea_pos : 0 < N.factorization a := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp haN)
  have heb_pos : 0 < N.factorization b := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hbN)
  have hec_pos : 0 < N.factorization c := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hcN)
  obtain ⟨q, _hq_mem, _hq_mod, _hq_exp_mod, h_even⟩ := euler_exponents ho hN
  have hcop_ab : a.Coprime b := (Nat.coprime_primes ha_prime hb_prime).mpr hab.ne
  have hcop_ac : a.Coprime c := (Nat.coprime_primes ha_prime hc_prime).mpr hac.ne
  have hcop_bc : b.Coprime c := (Nat.coprime_primes hb_prime hc_prime).mpr hbc.ne
  have habc_gt1 : 1 < a * b * c := by
    calc 1 < a := ha_prime.one_lt
      _ < a * b := lt_mul_of_one_lt_right ha_pos hb_prime.one_lt
      _ < a * b * c := lt_mul_of_one_lt_right (Nat.mul_pos ha_pos hb_pos) hc_prime.one_lt
  have hN_lt_2N : N < 2 * N := by
    have := hN.2
    omega
  by_cases hall2 : 2 ≤ N.factorization a ∧ 2 ≤ N.factorization b ∧ 2 ≤ N.factorization c
  · have hdvd : a ^ 2 * b ^ 2 * c ^ 2 ∣ N := by
      have ha_dvd := (ha_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr hall2.1
      have hb_dvd := (hb_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr hall2.2.1
      have hc_dvd := (hc_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr hall2.2.2
      have h1 : a ^ 2 * b ^ 2 ∣ N := nat_coprime_mul_dvd (hcop_ab.pow 2 2) ha_dvd hb_dvd
      have hcop_ab_c : (a ^ 2 * b ^ 2).Coprime (c ^ 2) :=
        (hcop_ac.pow 2 2).mul_left (hcop_bc.pow 2 2)
      exact nat_coprime_mul_dvd hcop_ab_c h1 hc_dvd
    have hle : (a * b * c) ^ 2 ≤ N := by
      calc (a * b * c) ^ 2 = a ^ 2 * b ^ 2 * c ^ 2 := by ring
        _ ≤ N := Nat.le_of_dvd hN.2 hdvd
    calc (a * b * c) ^ 5 < (a * b * c) ^ 6 := Nat.pow_lt_pow_right habc_gt1 (by decide)
      _ = ((a * b * c) ^ 2) ^ 3 := by ring
      _ ≤ N ^ 3 := Nat.pow_le_pow_left hle 3
      _ < (2 * N) ^ 3 := Nat.pow_lt_pow_left hN_lt_2N (by decide)
  · by_cases hea1 : N.factorization a = 1
    · have haq : a = q := by
        by_contra hne
        rcases h_even a hne with ⟨k, hk⟩; omega
      have hbq : b ≠ q := by rw [← haq]; exact hab.ne'
      have hcq : c ≠ q := by rw [← haq]; exact hac.ne'
      have heb2 : 2 ≤ N.factorization b := by
        rcases h_even b hbq with ⟨k, hk⟩; omega
      have hec2 : 2 ≤ N.factorization c := by
        rcases h_even c hcq with ⟨k, hk⟩; omega
      have hdvd : a * b ^ 2 * c ^ 2 ∣ N := by
        have ha_dvd : a ^ 1 ∣ N := (ha_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr hea1.ge
        have hb_dvd := (hb_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr heb2
        have hc_dvd := (hc_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr hec2
        have h1 : a ^ 1 * b ^ 2 ∣ N := nat_coprime_mul_dvd (hcop_ab.pow 1 2) ha_dvd hb_dvd
        have hcop_ab_c : (a ^ 1 * b ^ 2).Coprime (c ^ 2) :=
          (hcop_ac.pow 1 2).mul_left (hcop_bc.pow 2 2)
        simpa [pow_one] using nat_coprime_mul_dvd hcop_ab_c h1 hc_dvd
      have hle : a * b ^ 2 * c ^ 2 ≤ N := Nat.le_of_dvd hN.2 hdvd
      have ha2_lt : a ^ 2 < b * c := by nlinarith
      have hb5c5_pos : 0 < b ^ 5 * c ^ 5 := Nat.mul_pos (pow_pos hb_pos 5) (pow_pos hc_pos 5)
      calc (a * b * c) ^ 5 = (a ^ 3 * (b ^ 5 * c ^ 5)) * a ^ 2 := by ring
        _ < (a ^ 3 * (b ^ 5 * c ^ 5)) * (b * c) :=
          Nat.mul_lt_mul_of_pos_left ha2_lt (Nat.mul_pos (pow_pos ha_pos 3) hb5c5_pos)
        _ = (a * b ^ 2 * c ^ 2) ^ 3 := by ring
        _ ≤ N ^ 3 := Nat.pow_le_pow_left hle 3
        _ < (2 * N) ^ 3 := Nat.pow_lt_pow_left hN_lt_2N (by decide)
    · by_cases heb1 : N.factorization b = 1
      · have hbq : b = q := by
          by_contra hne
          rcases h_even b hne with ⟨k, hk⟩; omega
        have haq : a ≠ q := by rw [← hbq]; exact hab.ne
        have hcq : c ≠ q := by rw [← hbq]; exact hbc.ne'
        have hea2 : 2 ≤ N.factorization a := by
          rcases h_even a haq with ⟨k, hk⟩; omega
        have hec2 := even_pos_eq_two_or_four_le hec_pos (h_even c hcq)
        rcases hec2 with hec2 | hec4
        · have hbc4 : b * c ^ 4 < 2 * N := pair_e1_e2_bound ho hN hbN hcN hbc heb1 hec2
          have ha5_lt : a ^ 5 < c ^ 5 := Nat.pow_lt_pow_left hac (by decide)
          have hb2_lt : b ^ 2 < c ^ 2 := Nat.pow_lt_pow_left hbc (by decide)
          have h1 : a ^ 5 * b ^ 2 < c ^ 5 * c ^ 2 := Nat.mul_lt_mul'' ha5_lt hb2_lt
          have hb3c5_pos : 0 < b ^ 3 * c ^ 5 := Nat.mul_pos (pow_pos hb_pos 3) (pow_pos hc_pos 5)
          calc (a * b * c) ^ 5 = (a ^ 5 * b ^ 2) * (b ^ 3 * c ^ 5) := by ring
            _ < (c ^ 5 * c ^ 2) * (b ^ 3 * c ^ 5) := Nat.mul_lt_mul_of_pos_right h1 hb3c5_pos
            _ = (b * c ^ 4) ^ 3 := by ring
            _ < (2 * N) ^ 3 := Nat.pow_lt_pow_left hbc4 (by decide)
        · have hdvd : a ^ 2 * b * c ^ 4 ∣ N := by
            have ha_dvd := (ha_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr hea2
            have hb_dvd : b ^ 1 ∣ N := (hb_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr heb1.ge
            have hc_dvd := (hc_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr hec4
            have h1 : a ^ 2 * b ^ 1 ∣ N := nat_coprime_mul_dvd (hcop_ab.pow 2 1) ha_dvd hb_dvd
            have hcop_ab_c : (a ^ 2 * b ^ 1).Coprime (c ^ 4) :=
              (hcop_ac.pow 2 4).mul_left (hcop_bc.pow 1 4)
            simpa [pow_one] using nat_coprime_mul_dvd hcop_ab_c h1 hc_dvd
          have hle : a ^ 2 * b * c ^ 4 ≤ N := Nat.le_of_dvd hN.2 hdvd
          have hb2_lt : b ^ 2 < c ^ 7 := by
            have h1 : b ^ 2 < c ^ 2 := Nat.pow_lt_pow_left hbc (by decide)
            have h2 : c ^ 2 ≤ c ^ 7 := Nat.pow_le_pow_right hc_pos (by decide)
            exact h1.trans_le h2
          have ha_le : a ^ 5 ≤ a ^ 6 := Nat.pow_le_pow_right ha_pos (by decide)
          have h1 : a ^ 5 * b ^ 3 ≤ a ^ 6 * b ^ 3 := Nat.mul_le_mul_right _ ha_le
          have h2 : b ^ 2 * c ^ 5 < c ^ 7 * c ^ 5 :=
            Nat.mul_lt_mul_of_pos_right hb2_lt (pow_pos hc_pos 5)
          have hmul : (a ^ 5 * b ^ 3) * (b ^ 2 * c ^ 5) < (a ^ 6 * b ^ 3) * (c ^ 7 * c ^ 5) := by
            calc (a ^ 5 * b ^ 3) * (b ^ 2 * c ^ 5)
                ≤ (a ^ 6 * b ^ 3) * (b ^ 2 * c ^ 5) := Nat.mul_le_mul_right _ h1
              _ < (a ^ 6 * b ^ 3) * (c ^ 7 * c ^ 5) :=
                Nat.mul_lt_mul_of_pos_left h2 (Nat.mul_pos (pow_pos ha_pos 6) (pow_pos hb_pos 3))
          calc (a * b * c) ^ 5 = (a ^ 5 * b ^ 3) * (b ^ 2 * c ^ 5) := by ring
            _ < (a ^ 6 * b ^ 3) * (c ^ 7 * c ^ 5) := hmul
            _ = (a ^ 2 * b * c ^ 4) ^ 3 := by ring
            _ ≤ N ^ 3 := Nat.pow_le_pow_left hle 3
            _ < (2 * N) ^ 3 := Nat.pow_lt_pow_left hN_lt_2N (by decide)
      · have hec1 : N.factorization c = 1 := by omega
        have hcq : c = q := by
          by_contra hne
          rcases h_even c hne with ⟨k, hk⟩; omega
        have haq : a ≠ q := by rw [← hcq]; exact hac.ne
        have hbq : b ≠ q := by rw [← hcq]; exact hbc.ne
        have hea2 : 2 ≤ N.factorization a := by
          rcases h_even a haq with ⟨k, hk⟩; omega
        have heb2 := even_pos_eq_two_or_four_le heb_pos (h_even b hbq)
        have h_even_c : ∀ q_1, q_1 ≠ c → Even (N.factorization q_1) := fun q1 hne =>
          h_even q1 (hcq ▸ hne)
        rcases heb2 with heb2 | heb4
        · obtain ⟨K, i, hK1, _hKodd, _hcop_bK, _hcop_cK, hN_eq, hsigK, _hi0, hi1, hi2⟩ :=
            case_ec1_eb2_setup ho hN hbN hcN hbc heb2 hec1
          by_cases hmid : b ∣ i ∧ ¬ b ^ 2 ∣ i
          · exact triple_ec1_eb2_mid_dvd ho hN haN hbN hcN hab hbc heb2 hec1 hK1 hN_eq hsigK hi1 hi2 hmid.1 hmid.2
          · exact triple_ec1_eb2_not_mid ho hN haN hbN hcN hab hbc heb2 hec1 h_even_c hK1 hN_eq hsigK hi1 hi2 hmid
        · have hc3_lt : c ^ 3 < 3 * N := prime_cube_lt_three_mul hN ho hcN
          have hdvd : a ^ 2 * b ^ 4 * c ∣ N := by
            have ha_dvd := (ha_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr hea2
            have hb_dvd := (hb_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr heb4
            have hc_dvd : c ^ 1 ∣ N := (hc_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr hec1.ge
            have h1 : a ^ 2 * b ^ 4 ∣ N := nat_coprime_mul_dvd (hcop_ab.pow 2 4) ha_dvd hb_dvd
            have hcop_ab_c : (a ^ 2 * b ^ 4).Coprime (c ^ 1) :=
              (hcop_ac.pow 2 1).mul_left (hcop_bc.pow 4 1)
            simpa [pow_one] using nat_coprime_mul_dvd hcop_ab_c h1 hc_dvd
          have hle : a ^ 2 * b ^ 4 * c ≤ N := Nat.le_of_dvd hN.2 hdvd
          have h5_lt : a ^ 5 * b ^ 5 < a ^ 4 * b ^ 8 := by
            have h1 : a ^ 5 * b ^ 5 < a ^ 4 * b * b ^ 5 := by
              have : a ^ 5 < a ^ 4 * b := by
                calc a ^ 5 = a ^ 4 * a := by ring
                  _ < a ^ 4 * b := Nat.mul_lt_mul_of_pos_left hab (pow_pos ha_pos 4)
              exact Nat.mul_lt_mul_of_pos_right this (pow_pos hb_pos 5)
            have h2 : a ^ 4 * b ^ 6 ≤ a ^ 4 * b ^ 8 :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb_pos (by decide))
            calc a ^ 5 * b ^ 5 < a ^ 4 * b * b ^ 5 := h1
              _ = a ^ 4 * b ^ 6 := by ring
              _ ≤ a ^ 4 * b ^ 8 := h2
          calc (a * b * c) ^ 5 = (a ^ 5 * b ^ 5) * c ^ 5 := by ring
            _ < (a ^ 4 * b ^ 8) * c ^ 5 := Nat.mul_lt_mul_of_pos_right h5_lt (pow_pos hc_pos 5)
            _ = (a ^ 2 * b ^ 4 * c) ^ 2 * c ^ 3 := by ring
            _ < N ^ 2 * (3 * N) := by
              have h1 : (a ^ 2 * b ^ 4 * c) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hle 2
              calc (a ^ 2 * b ^ 4 * c) ^ 2 * c ^ 3
                  ≤ N ^ 2 * c ^ 3 := Nat.mul_le_mul_right _ h1
                _ < N ^ 2 * (3 * N) := Nat.mul_lt_mul_of_pos_left hc3_lt (pow_pos hN.2 2)
            _ < (2 * N) ^ 3 := by
              have hN3_pos : 0 < N ^ 3 := pow_pos hN.2 3
              calc N ^ 2 * (3 * N) = 3 * N ^ 3 := by ring
                _ < 8 * N ^ 3 := Nat.mul_lt_mul_of_pos_right (by decide) hN3_pos
                _ = (2 * N) ^ 3 := by ring

/-- For any three distinct prime factors `a < b < c` of an odd perfect number `N`, `a ^ 6 < 2 * N`. -/
theorem prime_pow_six_lt_two_mul_of_lt_lt {N a b c : ℕ} (ho : Odd N) (hN : N.Perfect)
    (haN : a ∈ N.primeFactors) (hbN : b ∈ N.primeFactors) (hcN : c ∈ N.primeFactors)
    (hab : a < b) (hbc : b < c) :
    a ^ 6 < 2 * N := by
  let s : Finset ℕ := {a, b, c}
  have hs_sub : s ⊆ N.primeFactors := by
    intro x hx
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : s.card = 3 := by
    have ha_nmem : a ∉ ({b, c} : Finset ℕ) := by simp [hab.ne, (hab.trans hbc).ne]
    rw [Finset.card_insert_of_notMem ha_nmem, Finset.card_pair hbc.ne]
  have ha_pos : 0 < a := (Nat.prime_of_mem_primeFactors haN).pos
  have hrank := prime_rank_bound hN ho s hs_sub (Finset.insert_nonempty _ _) ha_pos (t := a) (by
    intro x hx
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> omega)
  rw [hcard] at hrank
  norm_num at hrank
  omega

/-- The prime support of an odd perfect number is nonempty. -/
theorem primeFactors_nonempty {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    N.primeFactors.Nonempty := by
  have h4 := four_le_distinct_prime_factor_count ho hN
  exact Finset.card_pos.mp (by omega)

/-- Erasing the largest prime factor leaves a nonempty finset. -/
theorem primeFactors_erase_max'_nonempty {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (N.primeFactors.erase (N.primeFactors.max' (primeFactors_nonempty ho hN))).Nonempty := by
  have h4 := four_le_distinct_prime_factor_count ho hN
  have hc := Finset.max'_mem N.primeFactors (primeFactors_nonempty ho hN)
  exact Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hc]; omega)

/-- Erasing the two largest prime factors leaves a nonempty finset. -/
theorem primeFactors_erase_two_nonempty {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ((N.primeFactors.erase (N.primeFactors.max' (primeFactors_nonempty ho hN))).erase
      ((N.primeFactors.erase (N.primeFactors.max' (primeFactors_nonempty ho hN))).max'
        (primeFactors_erase_max'_nonempty ho hN))).Nonempty := by
  have h4 := four_le_distinct_prime_factor_count ho hN
  have hc := Finset.max'_mem N.primeFactors (primeFactors_nonempty ho hN)
  have hb := Finset.max'_mem _ (primeFactors_erase_max'_nonempty ho hN)
  exact Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem hc]; omega)

/-- Zelinsky's second-largest prime bound: `b ^ 5 < 2 * N`. -/
theorem second_largest_prime_pow_five_lt_two_mul {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    let c := N.primeFactors.max' (primeFactors_nonempty ho hN)
    let b := (N.primeFactors.erase c).max' (primeFactors_erase_max'_nonempty ho hN)
    b ^ 5 < 2 * N := by
  intro c b
  have hcN : c ∈ N.primeFactors := Finset.max'_mem _ _
  have hb_er : b ∈ N.primeFactors.erase c := Finset.max'_mem _ _
  have hbN : b ∈ N.primeFactors := Finset.mem_of_mem_erase hb_er
  have hbc : b < c := lt_of_le_of_ne (Finset.le_max' _ b hbN) (Finset.mem_erase.mp hb_er).1
  exact prime_pow_five_lt_two_mul_of_lt ho hN hbN hcN hbc

/-- Ranked top-three prime bounds: `a ^ 6 < 2 * N` and `(a * b * c) ^ 5 < (2 * N) ^ 3`. -/
theorem top_three_primes_bounds {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    let c := N.primeFactors.max' (primeFactors_nonempty ho hN)
    let b := (N.primeFactors.erase c).max' (primeFactors_erase_max'_nonempty ho hN)
    let a := ((N.primeFactors.erase c).erase b).max' (primeFactors_erase_two_nonempty ho hN)
    a ^ 6 < 2 * N ∧ (a * b * c) ^ 5 < (2 * N) ^ 3 := by
  intro c b a
  have hcN : c ∈ N.primeFactors := Finset.max'_mem _ _
  have hb_er : b ∈ N.primeFactors.erase c := Finset.max'_mem _ _
  have hbN : b ∈ N.primeFactors := Finset.mem_of_mem_erase hb_er
  have ha_er2 : a ∈ (N.primeFactors.erase c).erase b := Finset.max'_mem _ _
  have ha_er : a ∈ N.primeFactors.erase c := Finset.mem_of_mem_erase ha_er2
  have haN : a ∈ N.primeFactors := Finset.mem_of_mem_erase ha_er
  have hbc : b < c := lt_of_le_of_ne (Finset.le_max' _ b hbN) (Finset.mem_erase.mp hb_er).1
  have hab : a < b := lt_of_le_of_ne (Finset.le_max' _ a ha_er) (Finset.mem_erase.mp ha_er2).1
  exact ⟨prime_pow_six_lt_two_mul_of_lt_lt ho hN haN hbN hcN hab hbc,
    prime_triple_prod_pow_five_lt ho hN haN hbN hcN hab hbc⟩

end OddPerfect
