module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Euler's form for an odd perfect number

The argument follows the prime-power divisor-sum analysis of `euler_opn_form` in
`umpolungfish/odd-perfect-numbers` (Unlicense). See `research/EULER.md` for the
pinned source. We isolate the single even factor by divisibility by 4 and use
mathlib's square criterion on the remaining cofactor.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-- For a prime congruent to one, its divisor sum is congruent to the number of terms. -/
theorem sigma_modEq_of_one {p d : ℕ} (hp : p.Prime) (hd : p ≡ 1 [MOD d]) (a : ℕ) :
    sigma 1 (p ^ a) ≡ a + 1 [MOD d] := by
  rw [sigma_one_apply_prime_pow hp]
  suffices ∀ k, (∑ i ∈ Finset.range k, p ^ i) ≡ k [MOD d] from this _
  intro k
  induction k with
  | zero => simp [Nat.ModEq]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    exact ih.add (by simpa using hd.pow k)

/-- Pair consecutive powers in a geometric sum of even length. -/
private theorem succ_dvd_sum_even (p k : ℕ) :
    p + 1 ∣ ∑ i ∈ Finset.range (2 * k), p ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc,
      pow_succ p (2 * k), add_comm (p ^ (2 * k)) _, ← Nat.mul_succ]
    exact dvd_add ih (dvd_mul_left _ _)

/-- For odd exponent, the full sum of divisors contains the factor `p + 1`. -/
theorem succ_dvd_sigma_prime_pow {p a : ℕ} (hp : p.Prime) (ha : Odd a) :
    p + 1 ∣ sigma 1 (p ^ a) := by
  obtain ⟨k, hk⟩ := ha
  rw [sigma_one_apply_prime_pow hp, show a + 1 = 2 * (k + 1) by omega]
  exact succ_dvd_sum_even _ _

/-- Euler's special prime and the parity of every other prime's exponent. -/
theorem euler_exponents {n : ℕ} (hn : Odd n) (hperf : Nat.Perfect n) :
    ∃ p ∈ n.primeFactors, p % 4 = 1 ∧ n.factorization p % 4 = 1 ∧
      ∀ q : ℕ, q ≠ p → Even (n.factorization q) := by
  let f := fun p : ℕ => sigma 1 (p ^ n.factorization p)
  have hσ : sigma 1 n = 2 * n := by
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hn.pos).mp hperf
  have hprod : n.primeFactors.prod f = 2 * n :=
    (isMultiplicative_sigma.multiplicative_factorization _ hn.pos.ne').symm.trans hσ
  have h4 : ¬ 4 ∣ 2 * n := by have := hn.not_two_dvd_nat; omega
  obtain ⟨p, hpmem, hpeven⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff f).mp
    (show 2 ∣ n.primeFactors.prod f by rw [hprod]; exact dvd_mul_right _ _)
  have hprime := Nat.prime_of_mem_primeFactors hpmem
  have hpodd := hn.of_dvd_nat (Nat.dvd_of_mem_primeFactors hpmem)
  have hdvd : f p ∣ 2 * n := hprod ▸ Finset.dvd_prod_of_mem f hpmem
  have hlocal : ¬ 4 ∣ f p := fun h => h4 (h.trans hdvd)
  have parity (q : ℕ) (hq : q ∈ n.primeFactors) : f q % 2 = (n.factorization q + 1) % 2 :=
    sigma_modEq_of_one (Nat.prime_of_mem_primeFactors hq)
      (Nat.odd_iff.mp (hn.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq))) _
  have ha : n.factorization p % 2 = 1 := by have := parity p hpmem; omega
  have hp4 : p % 4 = 1 := by
    have hp2 := Nat.odd_iff.mp hpodd
    by_contra h
    have hd : 4 ∣ p + 1 := by omega
    apply hlocal
    apply hd.trans
    exact succ_dvd_sigma_prime_pow hprime (Nat.odd_iff.mpr ha)
  have hpσ : f p % 4 = (n.factorization p + 1) % 4 := sigma_modEq_of_one hprime hp4 _
  refine ⟨p, hpmem, hp4, by omega, ?_⟩
  intro q hqp
  by_cases hq : q ∈ n.primeFactors
  · have hrest : ¬ 2 ∣ (n.primeFactors.erase p).prod f := by
      intro hd
      apply h4
      rw [← hprod, ← Finset.mul_prod_erase _ _ hpmem]
      exact Nat.mul_dvd_mul hpeven hd
    have hqodd : ¬ 2 ∣ f q := fun h => hrest (h.trans
      (Finset.dvd_prod_of_mem f (Finset.mem_erase.mpr ⟨hqp, hq⟩)))
    have := parity q hq
    exact Nat.even_iff.mpr (by omega)
  · have : n.factorization q = 0 := Finsupp.notMem_support_iff.mp hq
    simp [this]

/-- Euler's form, including the coprimality condition on its square factor. -/
theorem euler_form {n : ℕ} (hn : Odd n) (hperf : Nat.Perfect n) :
    ∃ q a m : ℕ, q.Prime ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ ¬ q ∣ m ∧ n = q ^ a * m ^ 2 := by
  obtain ⟨q, hq, hq4, ha4, hEven⟩ := euler_exponents hn hperf
  have hprime := Nat.prime_of_mem_primeFactors hq
  have hsq : IsSquare (ordCompl[q] n) := by
    apply Nat.isSquare_iff_even_factorization.mpr
    intro r _
    rw [Nat.factorization_ordCompl]
    rcases eq_or_ne r q with rfl | h
    · simp
    · rw [Finsupp.erase_ne h]
      exact hEven r h
  obtain ⟨m, hm⟩ := hsq
  refine ⟨q, n.factorization q, m, hprime, hq4, ha4, ?_, ?_⟩
  · intro hd
    apply Nat.not_dvd_ordCompl hprime hn.pos.ne'
    rw [hm]
    exact hd.mul_right m
  · rw [pow_two, ← hm]
    exact (Nat.ordProj_mul_ordCompl_eq_self n q).symm

end OddPerfect
