module

public import OddPerfect.Quasiperfect
public import OddPerfect.AbundancyLimit
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
Support and prime-power restrictions for quasiperfect numbers (Cattaneo, Hagis–Cohen).
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private theorem quasiperfect_sigma_le_two_mul_add_one {N d : ℕ}
    (h : Quasiperfect N) (hd : d ∣ N) : sigma 1 d ≤ 2 * d + 1 := by
  have hN0 : N ≠ 0 := by rintro rfl; simp [Quasiperfect] at h
  have hdle : d ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hd
  rcases eq_or_lt_of_le hdle with rfl | hlt
  · exact le_of_eq h
  · have hdef : (∑ i ∈ d.properDivisors, i) < d :=
      quasiperfect_proper_divisor_deficient h (Nat.mem_properDivisors.mpr ⟨hd, hlt⟩)
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    omega

private theorem quasiperfect_support_product_bound {N : ℕ} (h : Quasiperfect N) :
    2 * (∏ p ∈ N.primeFactors, (p - 1)) < ∏ p ∈ N.primeFactors, p := by
  have hn : N ≠ 0 := by rintro rfl; simp [Quasiperfect] at h
  have hn1 : N ≠ 1 := by rintro rfl; simp [Quasiperfect] at h
  have hs : (∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p)) = 2 * N + 1 :=
    (isMultiplicative_sigma.multiplicative_factorization _ hn).symm.trans h
  have hne := Nat.nonempty_primeFactors.mpr (show 1 < N by omega)
  have loc {p e : ℕ} (hp : p.Prime) : sigma 1 (p ^ e) * (p - 1) < p ^ e * p := by
    rw [sigma_one_apply_prime_pow hp]
    have hg := geom_sum_mul_add (p - 1) (e + 1)
    rw [Nat.sub_add_cancel hp.one_lt.le, pow_succ] at hg
    omega
  have hprod := Finset.prod_lt_prod_of_nonempty₀
    (f := fun p : ℕ => sigma 1 (p ^ N.factorization p) * (p - 1))
    (g := fun p : ℕ => p ^ N.factorization p * p)
    (fun p hp => Nat.mul_pos (sigma_pos _ _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero))
      (Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt))
    (fun _ hp => loc (Nat.prime_of_mem_primeFactors hp)) hne
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hs,
    ← Nat.prod_primeFactors_pow_factorization hn] at hprod
  have hden : 0 < ∏ p ∈ N.primeFactors, (p - 1) :=
    Finset.prod_pos fun _ hp => Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt
  have hlt : N * (2 * ∏ p ∈ N.primeFactors, (p - 1)) < N * ∏ p ∈ N.primeFactors, p := by
    calc
      N * (2 * ∏ p ∈ N.primeFactors, (p - 1))
          = (2 * N) * (∏ p ∈ N.primeFactors, (p - 1)) := by ring
      _ < (2 * N + 1) * (∏ p ∈ N.primeFactors, (p - 1)) := by
          exact Nat.mul_lt_mul_of_pos_right (by omega) hden
      _ < N * ∏ p ∈ N.primeFactors, p := hprod
  exact Nat.lt_of_mul_lt_mul_left hlt

private theorem two_lt_prod_primeAbundancyLimit_of_quasiperfect {N : ℕ} (h : Quasiperfect N) :
    2 < ∏ p ∈ N.primeFactors, primeAbundancyLimit p := by
  simp only [primeAbundancyLimit, Finset.prod_div_distrib, ← Nat.cast_prod]
  have hden : 0 < ∏ p ∈ N.primeFactors, (p - 1) :=
    Finset.prod_pos fun _ hp => Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt
  rw [lt_div_iff₀ (by exact_mod_cast hden)]
  simpa only [Nat.cast_prod, Nat.cast_mul, Nat.cast_ofNat] using
    (Nat.cast_lt (α := ℚ)).mpr (quasiperfect_support_product_bound h)

/-- Every prime congruent to 3 or 5 modulo 8 dividing a quasiperfect number
divides it to at least the fourth power. -/
theorem fourth_pow_dvd_of_quasiperfect_mod_eight {N p : ℕ} (h : Quasiperfect N)
    (hp : p.Prime) (hmod : p % 8 = 3 ∨ p % 8 = 5) (hd : p ∣ N) : p ^ 4 ∣ N := by
  have hN0 : N ≠ 0 := by rintro rfl; simp [Quasiperfect] at h
  obtain ⟨_, s, hs⟩ := quasiperfect_odd_square h
  have heven : Even (N.factorization p) := by
    rw [hs, ← pow_two, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact ⟨s.factorization p, by ring⟩
  have hpos : 1 ≤ N.factorization p := (hp.dvd_iff_one_le_factorization hN0).mp hd
  by_contra h4
  have hlt4 : ¬ 4 ≤ N.factorization p := mt (hp.pow_dvd_iff_le_factorization hN0).mpr h4
  have heq2 : N.factorization p = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hp2 : p ^ 2 ∣ N := (hp.pow_dvd_iff_le_factorization hN0).mpr (by omega)
  have hp3 : ¬ p ^ 3 ∣ N := fun h3 => by
    have := (hp.pow_dvd_iff_le_factorization hN0).mp h3
    omega
  obtain ⟨b, hb, hcop⟩ := exists_coprime_cofactor_of_exact_prime_pow hp hp2 hp3
  have hdiv : sigma 1 (p ^ 2) ∣ sigma 1 N := by
    rw [hb, isMultiplicative_sigma.map_mul_of_coprime hcop]
    exact dvd_mul_right _ _
  have hmod8 := quasiperfect_sigma_divisors_mod_eight h hdiv
  rw [sigma_one_apply_prime_pow hp, sum_range_succ, sum_range_succ, sum_range_one] at hmod8
  have hval : (p ^ 0 + p ^ 1 + p ^ 2) % 8 = 5 ∨ (p ^ 0 + p ^ 1 + p ^ 2) % 8 = 7 := by
    rw [pow_zero, pow_one, pow_two, Nat.add_mod, Nat.add_mod 1, Nat.mul_mod]
    rcases hmod with h3 | h5
    · left; simp [h3]
    · right; simp [h5]
  rcases hmod8 with h1 | h3 <;> rcases hval with h5 | h7 <;> omega

/-- No quasiperfect number is divisible by 105. -/
theorem not_dvd_105_of_quasiperfect {N : ℕ} (h : Quasiperfect N) : ¬ 105 ∣ N := by
  intro h105
  have h3pow : 3 ^ 4 ∣ N := fourth_pow_dvd_of_quasiperfect_mod_eight h (by decide)
    (Or.inl (by decide)) ((by decide : 3 ∣ 105).trans h105)
  have h5pow : 5 ^ 4 ∣ N := fourth_pow_dvd_of_quasiperfect_mod_eight h (by decide)
    (Or.inr (by decide)) ((by decide : 5 ∣ 105).trans h105)
  have h7sq : 7 ^ 2 ∣ N := by
    have h7 : 7 ∣ N := (by decide : 7 ∣ 105).trans h105
    obtain ⟨_, s, rfl⟩ := quasiperfect_odd_square h
    have hs : 7 ∣ s := ((by decide : Nat.Prime 7).dvd_mul.mp h7).elim id id
    obtain ⟨k, rfl⟩ := hs
    exact ⟨k * k, by ring⟩
  have h35 : 3 ^ 4 * 5 ^ 4 ∣ N := (by decide : Nat.Coprime (3 ^ 4) (5 ^ 4)).mul_dvd_of_dvd_of_dvd h3pow h5pow
  have hdvd : 3 ^ 4 * 5 ^ 4 * 7 ^ 2 ∣ N :=
    (by decide : Nat.Coprime (3 ^ 4 * 5 ^ 4) (7 ^ 2)).mul_dvd_of_dvd_of_dvd h35 h7sq
  have hle := quasiperfect_sigma_le_two_mul_add_one h hdvd
  have hsig : sigma 1 (3 ^ 4 * 5 ^ 4 * 7 ^ 2) = sigma 1 (3 ^ 4) * sigma 1 (5 ^ 4) * sigma 1 (7 ^ 2) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (by decide),
      isMultiplicative_sigma.map_mul_of_coprime (by decide)]
  rw [hsig, sigma_one_apply_prime_pow (by decide), sigma_one_apply_prime_pow (by decide),
    sigma_one_apply_prime_pow (by decide)] at hle
  norm_num [Finset.sum_range_succ] at hle

private theorem not_dvd_3_5_11_or_13_of_quasiperfect {N r : ℕ} (h : Quasiperfect N)
    (h3 : 3 ∣ N) (h5 : 5 ∣ N) (hr : r ∣ N) (hrcase : r = 11 ∨ r = 13) : False := by
  have h3pow : 3 ^ 4 ∣ N := fourth_pow_dvd_of_quasiperfect_mod_eight h (by decide) (Or.inl (by decide)) h3
  have h5pow : 5 ^ 4 ∣ N := fourth_pow_dvd_of_quasiperfect_mod_eight h (by decide) (Or.inr (by decide)) h5
  have h35 : 3 ^ 4 * 5 ^ 4 ∣ N :=
    (by decide : Nat.Coprime (3 ^ 4) (5 ^ 4)).mul_dvd_of_dvd_of_dvd h3pow h5pow
  rcases hrcase with rfl | rfl
  · have h11pow : 11 ^ 4 ∣ N := fourth_pow_dvd_of_quasiperfect_mod_eight h (by decide) (Or.inl (by decide)) hr
    have hdvd : 3 ^ 4 * 5 ^ 4 * 11 ^ 4 ∣ N :=
      (by decide : Nat.Coprime (3 ^ 4 * 5 ^ 4) (11 ^ 4)).mul_dvd_of_dvd_of_dvd h35 h11pow
    have hle := quasiperfect_sigma_le_two_mul_add_one h hdvd
    have hsig : sigma 1 (3 ^ 4 * 5 ^ 4 * 11 ^ 4) =
        sigma 1 (3 ^ 4) * sigma 1 (5 ^ 4) * sigma 1 (11 ^ 4) := by
      rw [isMultiplicative_sigma.map_mul_of_coprime (by decide),
        isMultiplicative_sigma.map_mul_of_coprime (by decide)]
    rw [hsig, sigma_one_apply_prime_pow (by decide), sigma_one_apply_prime_pow (by decide),
      sigma_one_apply_prime_pow (by decide)] at hle
    norm_num [Finset.sum_range_succ] at hle
  · have h13pow : 13 ^ 4 ∣ N := fourth_pow_dvd_of_quasiperfect_mod_eight h (by decide) (Or.inr (by decide)) hr
    have hdvd : 3 ^ 4 * 5 ^ 4 * 13 ^ 4 ∣ N :=
      (by decide : Nat.Coprime (3 ^ 4 * 5 ^ 4) (13 ^ 4)).mul_dvd_of_dvd_of_dvd h35 h13pow
    have hle := quasiperfect_sigma_le_two_mul_add_one h hdvd
    have hsig : sigma 1 (3 ^ 4 * 5 ^ 4 * 13 ^ 4) =
        sigma 1 (3 ^ 4) * sigma 1 (5 ^ 4) * sigma 1 (13 ^ 4) := by
      rw [isMultiplicative_sigma.map_mul_of_coprime (by decide),
        isMultiplicative_sigma.map_mul_of_coprime (by decide)]
    rw [hsig, sigma_one_apply_prime_pow (by decide), sigma_one_apply_prime_pow (by decide),
      sigma_one_apply_prime_pow (by decide)] at hle
    norm_num [Finset.sum_range_succ] at hle

/-- Every quasiperfect number has at least four distinct prime factors. -/
theorem four_le_primeFactors_of_quasiperfect {N : ℕ} (h : Quasiperfect N) :
    4 ≤ N.primeFactors.card := by
  by_contra! hc
  have hodd := (quasiperfect_odd_square h).1
  have hnonneg (p : ℕ) : 0 ≤ primeAbundancyLimit p := by unfold primeAbundancyLimit; positivity
  by_cases h3 : 3 ∈ N.primeFactors
  · by_cases h5 : 5 ∈ N.primeFactors
    · let S := (N.primeFactors.erase 3).erase 5
      have h5' : 5 ∈ N.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨by decide, h5⟩
      have hcard : S.card ≤ 1 := by
        have h1 := Finset.card_erase_add_one h3
        have h2 := Finset.card_erase_add_one h5'
        dsimp [S]
        omega
      by_cases hbig : ∀ p ∈ S, 17 ≤ p
      · have hcard' : S.card ≤ ((Finset.Icc 17 17).filter Nat.Prime).card := by
          have : ((Finset.Icc 17 17).filter Nat.Prime).card = 1 := by decide
          omega
        have hsmall := prod_primeAbundancyLimit_le_interval (by decide : 1 < 17) S (a := 17)
          (fun p hp => ⟨Nat.prime_of_mem_primeFactors
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp)), hbig p hp⟩) hcard'
        have bound : ∏ p ∈ N.primeFactors, primeAbundancyLimit p ≤
            primeAbundancyLimit 3 * (primeAbundancyLimit 5 *
              ∏ p ∈ (Finset.Icc 17 17).filter Nat.Prime, primeAbundancyLimit p) := by
          rw [← Finset.mul_prod_erase _ _ h3, ← Finset.mul_prod_erase _ _ h5']
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsmall (hnonneg 5)) (hnonneg 3)
        have numeric : primeAbundancyLimit 3 * (primeAbundancyLimit 5 *
            ∏ p ∈ (Finset.Icc 17 17).filter Nat.Prime, primeAbundancyLimit p) < 2 := by
          decide +kernel
        exact (two_lt_prod_primeAbundancyLimit_of_quasiperfect h).not_ge (bound.trans numeric.le)
      · push Not at hbig
        obtain ⟨r, hrS, hrlt⟩ := hbig
        have hrmem := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hrS)
        have hrp := Nat.prime_of_mem_primeFactors hrmem
        have hrodd := hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hrmem)
        have hne3 : r ≠ 3 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hrS)).1
        have hne5 : r ≠ 5 := (Finset.mem_erase.mp hrS).1
        have hr2 := hrp.two_le
        have hrnot2 := hrodd.not_two_dvd_nat
        have hrcase : r = 7 ∨ r = 11 ∨ r = 13 := by
          interval_cases r <;> simp_all <;> exact absurd hrp (by decide)
        have h3dvd : 3 ∣ N := Nat.dvd_of_mem_primeFactors h3
        have h5dvd : 5 ∣ N := Nat.dvd_of_mem_primeFactors h5
        have hrdvd : r ∣ N := Nat.dvd_of_mem_primeFactors hrmem
        rcases hrcase with rfl | h1113
        · have h15 : 15 ∣ N := (by decide : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd h3dvd h5dvd
          exact not_dvd_105_of_quasiperfect h
            ((by decide : Nat.Coprime 15 7).mul_dvd_of_dvd_of_dvd h15 hrdvd)
        · exact not_dvd_3_5_11_or_13_of_quasiperfect h h3dvd h5dvd hrdvd h1113
    · let S := N.primeFactors.erase 3
      have hcard : S.card ≤ ((Finset.Icc 7 11).filter Nat.Prime).card := by
        have h1 := Finset.card_erase_add_one h3
        have : ((Finset.Icc 7 11).filter Nat.Prime).card = 2 := by decide
        dsimp [S]
        omega
      have hsmall := prod_primeAbundancyLimit_le_interval (by decide : 1 < 11) S (a := 7)
        (fun p hp => by
          have hpmem := Finset.mem_of_mem_erase hp
          have hpp := Nat.prime_of_mem_primeFactors hpmem
          have hpodd := hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hpmem)
          have hne3 : p ≠ 3 := (Finset.mem_erase.mp hp).1
          have hne5 : p ≠ 5 := fun h5' => h5 (h5' ▸ hpmem)
          have hne4 : p ≠ 4 := fun h4 => by rw [h4] at hpp; exact absurd hpp (by decide)
          have hne6 : p ≠ 6 := fun h6 => by rw [h6] at hpp; exact absurd hpp (by decide)
          have := hpp.two_le
          have := hpodd.not_two_dvd_nat
          exact ⟨hpp, by omega⟩) hcard
      have bound : ∏ p ∈ N.primeFactors, primeAbundancyLimit p ≤
          primeAbundancyLimit 3 *
            ∏ p ∈ (Finset.Icc 7 11).filter Nat.Prime, primeAbundancyLimit p := by
        rw [← Finset.mul_prod_erase _ _ h3]
        exact mul_le_mul_of_nonneg_left hsmall (hnonneg 3)
      have numeric : primeAbundancyLimit 3 *
          (∏ p ∈ (Finset.Icc 7 11).filter Nat.Prime, primeAbundancyLimit p) < 2 := by
        decide +kernel
      exact (two_lt_prod_primeAbundancyLimit_of_quasiperfect h).not_ge (bound.trans numeric.le)
  · have hcard : N.primeFactors.card ≤ ((Finset.Icc 5 11).filter Nat.Prime).card := by
      have : ((Finset.Icc 5 11).filter Nat.Prime).card = 3 := by decide
      omega
    have hsmall := prod_primeAbundancyLimit_le_interval (by decide : 1 < 11) N.primeFactors (a := 5)
      (fun p hp => by
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpodd := hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
        have hne3 : p ≠ 3 := fun h3' => h3 (h3' ▸ hp)
        have hne4 : p ≠ 4 := fun h4 => by rw [h4] at hpp; exact absurd hpp (by decide)
        have := hpp.two_le
        have := hpodd.not_two_dvd_nat
        exact ⟨hpp, by omega⟩) hcard
    have numeric : (∏ p ∈ (Finset.Icc 5 11).filter Nat.Prime, primeAbundancyLimit p) < 2 := by
      decide +kernel
    exact (two_lt_prod_primeAbundancyLimit_of_quasiperfect h).not_ge (hsmall.trans numeric.le)

/-- Every quasiperfect number not divisible by 3 has at least seven distinct prime factors. -/
theorem seven_le_primeFactors_of_quasiperfect_three_free {N : ℕ} (h : Quasiperfect N)
    (h3 : ¬ 3 ∣ N) : 7 ≤ N.primeFactors.card := by
  by_contra! hc
  have hodd := (quasiperfect_odd_square h).1
  have hcard : N.primeFactors.card ≤ ((Finset.Icc 5 19).filter Nat.Prime).card := by
    have : ((Finset.Icc 5 19).filter Nat.Prime).card = 6 := by decide
    omega
  have hsmall := prod_primeAbundancyLimit_le_interval (by decide : 1 < 19) N.primeFactors (a := 5)
    (fun p hp => by
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpodd := hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
      have hne3 : p ≠ 3 := fun h3' => h3 (h3' ▸ Nat.dvd_of_mem_primeFactors hp)
      have hne4 : p ≠ 4 := fun h4 => by rw [h4] at hpp; exact absurd hpp (by decide)
      have := hpp.two_le
      have := hpodd.not_two_dvd_nat
      exact ⟨hpp, by omega⟩) hcard
  have numeric : (∏ p ∈ (Finset.Icc 5 19).filter Nat.Prime, primeAbundancyLimit p) < 2 := by
    decide +kernel
  exact (two_lt_prod_primeAbundancyLimit_of_quasiperfect h).not_ge (hsmall.trans numeric.le)

end OddPerfect
