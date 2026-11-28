module

public import OddPerfect.Forcing
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Strict abundancy bounds in terms of the support of the prime factorization. -/

public section

namespace OddPerfect

open ArithmeticFunction

/-- Multiplying the strict geometric bounds at every prime factor clears all
denominators in the comparison of abundancy with its limiting Euler product. -/
theorem perfect_support_product_bound {N : ℕ} (hN : N.Perfect) :
    2 * (∏ p ∈ N.primeFactors, (p - 1)) < ∏ p ∈ N.primeFactors, p := by
  have hn := hN.2.ne'
  have hs : (∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p)) = 2 * N := by
    trans sigma 1 N
    · exact (isMultiplicative_sigma.multiplicative_factorization _ hn).symm
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN
  have hn1 : N ≠ 1 := by
    rintro rfl
    exact (by decide : ¬ Nat.Perfect 1) hN
  have hne := Nat.nonempty_primeFactors.mpr (show 1 < N by omega)
  have loc {p e : ℕ} (hp : p.Prime) : sigma 1 (p ^ e) * (p - 1) < p ^ e * p := by
    rw [sigma_one_apply_prime_pow hp]
    have h := geom_sum_mul_add (p - 1) (e + 1)
    rw [Nat.sub_add_cancel hp.one_lt.le, pow_succ] at h
    omega
  have hprod := Finset.prod_lt_prod_of_nonempty₀
    (f := fun p : ℕ => sigma 1 (p ^ N.factorization p) * (p - 1))
    (g := fun p : ℕ => p ^ N.factorization p * p)
    (fun p hp => Nat.mul_pos (sigma_pos _ _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero))
      (Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt))
    (fun _ hp => loc (Nat.prime_of_mem_primeFactors hp)) hne
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hs,
    ← Nat.prod_primeFactors_pow_factorization hn] at hprod
  exact Nat.lt_of_mul_lt_mul_left (by simpa [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc]
    using hprod : N * (2 * ∏ p ∈ N.primeFactors, (p - 1)) < N * ∏ p ∈ N.primeFactors, p)

/-- The limiting abundancy of a positive prime power as its exponent increases. -/
@[expose] def primeAbundancyLimit (p : ℕ) : ℚ := (p : ℚ) / ((p - 1 : ℕ) : ℚ)

/-- The product of the limiting prime-power abundancies strictly exceeds two
for the prime support of every perfect number. -/
theorem two_lt_prod_primeAbundancyLimit {N : ℕ} (hN : N.Perfect) :
    2 < ∏ p ∈ N.primeFactors, primeAbundancyLimit p := by
  simp only [primeAbundancyLimit, Finset.prod_div_distrib, ← Nat.cast_prod]
  have hden : 0 < ∏ p ∈ N.primeFactors, (p - 1) :=
    Finset.prod_pos fun _ hp => Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt
  rw [lt_div_iff₀ (by exact_mod_cast hden)]
  simpa only [Nat.cast_prod, Nat.cast_mul, Nat.cast_ofNat] using
    (Nat.cast_lt (α := ℚ)).mpr (perfect_support_product_bound hN)

/-- The limiting abundancy decreases with the prime. -/
theorem primeAbundancyLimit_antitone {p q : ℕ} (hp : 1 < p) (hpq : p ≤ q) :
    primeAbundancyLimit q ≤ primeAbundancyLimit p := by
  dsimp [primeAbundancyLimit]
  rw [div_le_div_iff₀ (by exact_mod_cast Nat.sub_pos_of_lt (hp.trans_le hpq))
    (by exact_mod_cast Nat.sub_pos_of_lt hp)]
  have hpred (a : ℕ) (ha : 1 ≤ a) : ((a - 1 : ℕ) : ℚ) = (a : ℚ) - 1 := by
    rw [Nat.cast_sub ha, Nat.cast_one]
  rw [hpred p hp.le, hpred q (hp.le.trans hpq)]
  have h : (p : ℚ) ≤ q := by exact_mod_cast hpq
  nlinarith

/-- A finite set t dominates s if the extra primes are above a cutoff and
the missing primes are below it. -/
theorem prod_primeAbundancyLimit_le_of_cut {b : ℕ} (hb : 1 < b) (s t : Finset ℕ)
    (hcard : s.card ≤ t.card) (hleft : ∀ p ∈ s \ t, b ≤ p)
    (hright : ∀ p ∈ t \ s, 1 < p ∧ p ≤ b) :
    (∏ p ∈ s, primeAbundancyLimit p) ≤ ∏ p ∈ t, primeAbundancyLimit p := by
  have hn (p : ℕ) : 0 ≤ primeAbundancyLimit p := by unfold primeAbundancyLimit; positivity
  have hb1 : 1 ≤ primeAbundancyLimit b := by
    rw [primeAbundancyLimit, le_div_iff₀ (by exact_mod_cast Nat.sub_pos_of_lt hb), one_mul]
    exact_mod_cast Nat.sub_le b 1
  have hdiff : (s \ t).card ≤ (t \ s).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_comm t s]
    omega
  have hextra : (∏ p ∈ s \ t, primeAbundancyLimit p) ≤ primeAbundancyLimit b ^ (s \ t).card := by
    calc
      _ ≤ ∏ _p ∈ s \ t, primeAbundancyLimit b := by
        apply Finset.prod_le_prod₀ (fun p _ => hn p)
        intro p hp
        exact primeAbundancyLimit_antitone hb (hleft p hp)
      _ = _ := by simp
  have hmissing : primeAbundancyLimit b ^ (t \ s).card ≤ ∏ p ∈ t \ s, primeAbundancyLimit p := by
    calc
      _ = ∏ _p ∈ t \ s, primeAbundancyLimit b := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod₀ (fun _ _ => hn b)
        intro p hp
        exact primeAbundancyLimit_antitone (hright p hp).1 (hright p hp).2
  have bound := (hextra.trans (pow_le_pow_right₀ hb1 hdiff)).trans hmissing
  calc
    _ = (∏ p ∈ s ∩ t, primeAbundancyLimit p) * ∏ p ∈ s \ t, primeAbundancyLimit p :=
      (s.prod_inter_mul_prod_sdiff t _).symm
    _ ≤ (∏ p ∈ s ∩ t, primeAbundancyLimit p) * ∏ p ∈ t \ s, primeAbundancyLimit p :=
      mul_le_mul_of_nonneg_left bound (Finset.prod_nonneg fun p _ => hn p)
    _ = _ := by rw [Finset.inter_comm s t, t.prod_inter_mul_prod_sdiff s _]

/-- The first primes above a threshold maximize the limiting abundancy for a
fixed upper bound on the number of factors. -/
theorem prod_primeAbundancyLimit_le_interval {a b : ℕ} (hb : 1 < b)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ a ≤ p)
    (hcard : s.card ≤ ((Finset.Icc a b).filter Nat.Prime).card) :
    (∏ p ∈ s, primeAbundancyLimit p) ≤
      ∏ p ∈ (Finset.Icc a b).filter Nat.Prime, primeAbundancyLimit p := by
  apply prod_primeAbundancyLimit_le_of_cut hb _ _ hcard
  · intro p hp
    obtain ⟨hps, hpt⟩ := Finset.mem_sdiff.mp hp
    by_contra! h
    exact hpt (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hs p hps).2, h.le⟩, (hs p hps).1⟩)
  · intro p hp
    obtain ⟨hint, hprime⟩ := Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1
    exact ⟨hprime.one_lt, (Finset.mem_Icc.mp hint).2⟩

/-- Retain one exact local factor and bound all other components by their limits. -/
theorem abundancy_bound_with_exact_prime {N p : ℕ} (hN : N.Perfect) (hp : p ∈ N.primeFactors) :
    2 ≤ ((sigma 1 (p ^ N.factorization p) : ℕ) : ℚ) / (p ^ N.factorization p : ℕ) *
      ∏ q ∈ N.primeFactors.erase p, primeAbundancyLimit q := by
  let f (q : ℕ) : ℚ := ((sigma 1 (q ^ N.factorization q) : ℕ) : ℚ) /
    ((q ^ N.factorization q : ℕ) : ℚ)
  have hn := hN.2.ne'
  have hnum : (∏ q ∈ N.primeFactors, sigma 1 (q ^ N.factorization q)) = 2 * N := by
    trans sigma 1 N
    · exact (isMultiplicative_sigma.multiplicative_factorization _ hn).symm
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN
  have hprod : N.primeFactors.prod f = 2 := by
    unfold f
    rw [Finset.prod_div_distrib]
    simp only [← Nat.cast_prod, hnum, ← Nat.prod_primeFactors_pow_factorization hn]
    simp [Nat.cast_mul, hn]
  have hpos (q : ℕ) : 0 ≤ f q := by unfold f; positivity
  have hle (q : ℕ) (hq : q ∈ N.primeFactors) : f q ≤ primeAbundancyLimit q := by
    have hr := Nat.prime_of_mem_primeFactors hq
    have hc := geom_sum_mul_add (q - 1) (N.factorization q + 1)
    rw [Nat.sub_add_cancel hr.one_lt.le, pow_succ, ← sigma_one_apply_prime_pow hr] at hc
    unfold f primeAbundancyLimit
    rw [div_le_div_iff₀ (by exact_mod_cast Nat.pow_pos hr.pos) (by exact_mod_cast Nat.sub_pos_of_lt hr.one_lt)]
    exact_mod_cast (show (sigma 1 (q ^ N.factorization q)) * (q - 1) ≤ q * q ^ N.factorization q by
      rw [Nat.mul_comm q]
      omega)
  calc
    (2 : ℚ) = f p * ∏ q ∈ N.primeFactors.erase p, f q :=
      hprod.symm.trans (Finset.mul_prod_erase _ _ hp).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun q _ => hpos q) (fun q hq => hle q (Finset.mem_of_mem_erase hq))) (hpos p)

end OddPerfect
