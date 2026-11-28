module

public import OddPerfect.AbundancyLimit
public import OddPerfect.SupportSieve
public import OddPerfect.Abundance
import OddPerfect.Thirteen
import OddPerfect.Euler
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Positivity

/-! Bounds for small numbers of distinct prime factors. -/

public section

namespace OddPerfect

/-- Every odd perfect number has at least four distinct prime factors. -/
theorem four_le_distinct_prime_factor_count {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    4 ≤ N.primeFactors.card := by
  by_contra! hc
  obtain ⟨q, hq, hbig⟩ := SupportSieve.exists_prime_gt_nineteen hN ho
  have hcard : (N.primeFactors.erase q).card ≤ ((Finset.Icc 3 5).filter Nat.Prime).card := by
    have := Finset.card_erase_add_one hq
    have : ((Finset.Icc 3 5).filter Nat.Prime).card = 2 := by decide
    omega
  have hsmall := prod_primeAbundancyLimit_le_interval (by decide : 1 < 5)
    (N.primeFactors.erase q) (a := 3) (by
      intro p hp
      have hmem := Finset.mem_of_mem_erase hp
      have hprime := Nat.prime_of_mem_primeFactors hmem
      have hodd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hmem)
      have := hprime.two_le
      have := hodd.not_two_dvd_nat
      exact ⟨hprime, by omega⟩) hcard
  have hqbound : primeAbundancyLimit q ≤ primeAbundancyLimit 19 :=
    primeAbundancyLimit_antitone (by decide) hbig.le
  have hnonneg (p : ℕ) : 0 ≤ primeAbundancyLimit p := by unfold primeAbundancyLimit; positivity
  have bound := mul_le_mul hqbound hsmall (Finset.prod_nonneg fun p _ => hnonneg p) (hnonneg 19)
  rw [Finset.mul_prod_erase _ _ hq] at bound
  have numeric : primeAbundancyLimit 19 *
      (∏ p ∈ (Finset.Icc 3 5).filter Nat.Prime, primeAbundancyLimit p) < 2 := by decide +kernel
  exact (two_lt_prod_primeAbundancyLimit hN).not_ge (bound.trans numeric.le)

/-- Once a fourth prime reaches 257, the abundancy bound and the exclusion
of 105 leave only two possibilities for the other three primes. -/
theorem four_prime_support_of_large_prime {N R : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hω : N.primeFactors.card ≤ 4) (hR : R ∈ N.primeFactors) (hlarge : 257 ≤ R) :
    ∃ s : ℕ, (s = 11 ∨ s = 13) ∧ N.primeFactors = {3, 5, s, R} := by
  let S := N.primeFactors.erase R
  have hRlimit := primeAbundancyLimit_antitone (by decide : 1 < 257) hlarge
  have hnonneg (q : ℕ) : 0 ≤ primeAbundancyLimit q := by unfold primeAbundancyLimit; positivity
  have cut (t excluded : Finset ℕ) (b : ℕ)
      (hb : 1 < b) (ht : t.card = 3) (hlow : ∀ q ∈ t, 1 < q ∧ q ≤ b)
      (hcover : ∀ q : Fin b, q.val.Prime → ¬ 2 ∣ q.val → q.val ∈ excluded ∨ q.val ∈ t)
      (habsent : ∀ q ∈ excluded, q ∉ N.primeFactors)
      (hnum : primeAbundancyLimit 257 * t.prod primeAbundancyLimit < 2) : False := by
    have hcard : S.card ≤ t.card := by have := Finset.card_erase_add_one hR; dsimp [S]; omega
    have hprod := prod_primeAbundancyLimit_le_of_cut hb S t hcard (by
      intro q hq
      obtain ⟨hqs, hqt⟩ := Finset.mem_sdiff.mp hq
      have hqn := Finset.mem_of_mem_erase hqs
      by_contra! h
      rcases hcover ⟨q, h⟩ (Nat.prime_of_mem_primeFactors hqn)
        (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hqn)).not_two_dvd_nat with he | ht
      · exact habsent q he hqn
      · exact hqt ht) (fun q hq => hlow q (Finset.mem_sdiff.mp hq).1)
    have h := mul_le_mul hRlimit hprod (Finset.prod_nonneg fun q _ => hnonneg q) (hnonneg 257)
    rw [show primeAbundancyLimit R * S.prod primeAbundancyLimit =
      N.primeFactors.prod primeAbundancyLimit from Finset.mul_prod_erase _ _ hR] at h
    exact (two_lt_prod_primeAbundancyLimit hN).not_ge (h.trans hnum.le)
  have h3 : 3 ∈ N.primeFactors := by
    by_contra h
    exact cut {5,7,11} {3} 11 (by decide) (by decide) (by decide) (by decide) (by simpa only [Finset.mem_singleton, forall_eq] using h)
      (by decide +kernel)
  have h5 : 5 ∈ N.primeFactors := by
    by_contra h
    exact cut {3,7,11} {5} 11 (by decide) (by decide) (by decide) (by decide) (by simpa only [Finset.mem_singleton, forall_eq] using h)
      (by decide +kernel)
  have h7 : 7 ∉ N.primeFactors := by
    intro h7
    have h15 : 15 ∣ N := (by decide : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd
      (Nat.dvd_of_mem_primeFactors h3) (Nat.dvd_of_mem_primeFactors h5)
    exact not_dvd_105_of_odd_perfect hN ho
      ((by decide : Nat.Coprime 15 7).mul_dvd_of_dvd_of_dvd h15 (Nat.dvd_of_mem_primeFactors h7))
  have hlast : 11 ∈ N.primeFactors ∨ 13 ∈ N.primeFactors := by
    by_contra! h
    exact cut {3,5,17} {7,11,13} 17 (by decide) (by decide) (by decide) (by decide)
      (by simpa only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq] using And.intro h7 h) (by decide +kernel)
  have complete (s : ℕ) (hs : s = 11 ∨ s = 13) (hmem : s ∈ N.primeFactors) :
      N.primeFactors = {3,5,s,R} := by
    have hsub : ({3,5,s,R} : Finset ℕ) ⊆ N.primeFactors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hcard : ({3,5,s,R} : Finset ℕ).card = 4 := by
      rcases hs with rfl | rfl <;> simp [show 3 ≠ R by omega, show 5 ≠ R by omega,
        show 11 ≠ R by omega, show 13 ≠ R by omega]
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  rcases hlast with h | h
  · exact ⟨11, Or.inl rfl, complete _ (Or.inl rfl) h⟩
  · exact ⟨13, Or.inr rfl, complete _ (Or.inr rfl) h⟩

/-- In either of the two remaining supports a small exact exponent gives
deficiency; raising all three small exponents gives an abundant divisor. -/
theorem five_le_distinct_prime_factor_count_of_large {N R : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hR : R ∈ N.primeFactors) (hlarge : 257 ≤ R) : 5 ≤ N.primeFactors.card := by
  by_contra! hω
  obtain ⟨s, hs, hset⟩ := four_prime_support_of_large_prime ho hN (by omega) hR hlarge
  have hslo : 11 ≤ s := by rcases hs with rfl | rfl <;> decide
  have hshi : s ≤ 13 := by rcases hs with rfl | rfl <;> decide
  have h3m : 3 ∈ N.primeFactors := by rw [hset]; simp
  have h5m : 5 ∈ N.primeFactors := by rw [hset]; simp
  have hsm : s ∈ N.primeFactors := by rw [hset]; simp
  have h7 : ¬ 7 ∣ N := by
    intro hd
    have hm := Nat.mem_primeFactors.mpr ⟨(by decide : Nat.Prime 7), hd, hN.2.ne'⟩
    rw [hset] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  let L := primeAbundancyLimit
  have hnonneg (q : ℕ) : 0 ≤ L q := by unfold L primeAbundancyLimit; positivity
  have hsr := mul_le_mul (primeAbundancyLimit_antitone (by decide : 1 < 11) hslo)
    (primeAbundancyLimit_antitone (by decide : 1 < 257) hlarge) (hnonneg R) (hnonneg 11)
  have close (a b : ℕ) (ha : a ∈ N.primeFactors) (hblt : b < s)
      (herase : N.primeFactors.erase a = {b,s,R}) (k : ℚ) (hk : 0 ≤ k)
      (hlocal : ((ArithmeticFunction.sigma 1 (a ^ N.factorization a) : ℕ) : ℚ) /
        ((a ^ N.factorization a : ℕ) : ℚ) = k)
      (hnumeric : k * (L b * (L 11 * L 257)) < 2) : False := by
    have hbound := abundancy_bound_with_exact_prime hN ha
    rw [herase, hlocal] at hbound
    have hrest : (∏ p ∈ ({b,s,R} : Finset ℕ), L p) = L b * (L s * L R) := by
      simp [show b ≠ s by omega, show b ≠ R by omega, show s ≠ R by omega]
    change 2 ≤ k * ∏ p ∈ ({b,s,R} : Finset ℕ), L p at hbound
    rw [hrest] at hbound
    exact hnumeric.not_ge (hbound.trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsr (hnonneg b)) hk))
  have h5ne : N.factorization 5 ≠ 1 := by
    intro h5
    apply close 5 3 h5m (by omega) _ (6/5) (by norm_num) _ (by decide +kernel)
    · rw [hset]
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      omega
    · rw [h5]
      decide +kernel
  have h5pos := ((by decide : Nat.Prime 5).dvd_iff_one_le_factorization hN.2.ne').mp
    (Nat.dvd_of_mem_primeFactors h5m)
  have h25 : 25 ∣ N := ((by decide : Nat.Prime 5).pow_dvd_iff_le_factorization
    (k := 2) hN.2.ne').2 (by omega)
  have hss : s ^ 2 ∣ N := by
    have hsN := Nat.dvd_of_mem_primeFactors hsm
    rcases hs with rfl | rfl
    · exact sq_dvd_of_prime_mod_four_three hN ho (by decide) (by decide) hsN
    · by_contra hnot
      exact h7 (seven_dvd_of_exact_thirteen_pow (e := 1) hN (by simpa using hsN) hnot (by decide))
  have h81 : ¬ 81 ∣ N := by
    intro hd
    have hcop : (81 * 25).Coprime (s ^ 2) := by rcases hs with rfl | rfl <;> decide
    have hab : Nat.Abundant (81 * 25 * s ^ 2) := by
      rw [Nat.abundant_iff_sum_divisors, hcop.sum_divisors_mul,
        (by decide : Nat.Coprime 81 25).sum_divisors_mul]
      rcases hs with rfl | rfl <;> decide +kernel
    have hdiv := hcop.mul_dvd_of_dvd_of_dvd ((by decide : Nat.Coprime 81 25).mul_dvd_of_dvd_of_dvd hd h25) hss
    exact ((Nat.perfect_iff_not_abundant_and_not_deficient hN.2.ne).mp hN).1
      (hab.of_dvd hdiv hN.2.ne')
  have h3e : N.factorization 3 = 2 := by
    obtain ⟨p, _, hp4, _, he⟩ := euler_exponents ho hN
    obtain ⟨k, hk⟩ := he 3 (by omega)
    have hpos := (Nat.prime_three.dvd_iff_one_le_factorization hN.2.ne').mp
      (Nat.dvd_of_mem_primeFactors h3m)
    have hsmall : ¬ 4 ≤ N.factorization 3 :=
      fun h => h81 ((Nat.prime_three.pow_dvd_iff_le_factorization hN.2.ne').2 h)
    omega
  apply close 3 5 h3m (by omega) _ (13/9) (by norm_num) _ (by decide +kernel)
  · rw [hset]
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    omega
  · rw [h3e]
    decide +kernel

/-- If 3 is absent and one prime is at least 41, the remaining six smallest
possible primes already give too small a limiting abundancy. -/
theorem eight_distinct_of_three_free_of_large {N R : ℕ} (ho : Odd N) (hN : N.Perfect)
    (h3 : ¬ 3 ∣ N) (hR : R ∈ N.primeFactors) (hbig : 41 ≤ R) :
    8 ≤ N.primeFactors.card := by
  by_contra! hc
  have hcard : (N.primeFactors.erase R).card ≤ ((Finset.Icc 5 19).filter Nat.Prime).card := by
    have := Finset.card_erase_add_one hR
    have : ((Finset.Icc 5 19).filter Nat.Prime).card = 6 := by decide
    omega
  have hsmall := prod_primeAbundancyLimit_le_interval (by decide : 1 < 19)
    (N.primeFactors.erase R) (a := 5) (by
      intro q hq
      have hmem := Finset.mem_of_mem_erase hq
      have hp := Nat.prime_of_mem_primeFactors hmem
      have hd := Nat.dvd_of_mem_primeFactors hmem
      have hnot := (ho.of_dvd_nat hd).not_two_dvd_nat
      have hclass : ∀ a : Fin 5, a.val.Prime → ¬ 2 ∣ a.val → a.val = 3 := by decide
      exact ⟨hp, by
        by_contra! h
        have heq : q = 3 := hclass ⟨q, h⟩ hp hnot
        exact h3 (heq ▸ hd)⟩) hcard
  have hnonneg (p : ℕ) : 0 ≤ primeAbundancyLimit p := by unfold primeAbundancyLimit; positivity
  have bound := mul_le_mul (primeAbundancyLimit_antitone (by decide : 1 < 41) hbig) hsmall
    (Finset.prod_nonneg fun p _ => hnonneg p) (hnonneg 41)
  rw [Finset.mul_prod_erase _ _ hR] at bound
  have numeric : primeAbundancyLimit 41 *
      (∏ p ∈ (Finset.Icc 5 19).filter Nat.Prime, primeAbundancyLimit p) < 2 := by decide +kernel
  exact (two_lt_prod_primeAbundancyLimit hN).not_ge (bound.trans numeric.le)

/-- Sylvester's five-distinct-prime bound, using the certified support sieve. -/
theorem five_le_distinct_prime_factor_count {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    5 ≤ N.primeFactors.card := by
  obtain ⟨R, hR, hbig⟩ := SupportSieve.exists_prime_gt_257 hN ho
  exact five_le_distinct_prime_factor_count_of_large ho hN hR hbig.le

/-- Sylvester's eight-distinct-prime bound when 3 is absent. -/
theorem eight_le_distinct_prime_factor_count_of_three_free {N : ℕ} (ho : Odd N)
    (hN : N.Perfect) (h3 : ¬3 ∣ N) : 8 ≤ N.primeFactors.card := by
  obtain ⟨R, hR, hbig⟩ := SupportSieve.exists_prime_gt_257 hN ho
  exact eight_distinct_of_three_free_of_large ho hN h3 hR (by omega)

end OddPerfect
