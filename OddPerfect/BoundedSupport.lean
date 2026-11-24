module

public import OddPerfect.CyclotomicOrders
import Mathlib.Data.Nat.Factorial.Basic

public section

namespace OddPerfect

/-- The full component length occurs as an order at another prime divisor. -/
theorem exists_larger_prime_than_length {N p : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hp : p ∈ N.primeFactors) :
    ∃ r ∈ N.primeFactors.erase p, N.factorization p + 1 < r := by
  have he : N.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  obtain ⟨r, hr, _, hd⟩ := exists_forced_order_of_length hN ho
    (Nat.prime_of_mem_primeFactors hp) rfl (by omega : 1 < N.factorization p + 1) dvd_rfl
  have hrp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hr)
  have hr2 := hrp.two_le
  have := Nat.le_of_dvd (by omega : 0 < r - 1) hd
  exact ⟨r, hr, by omega⟩

/-- For prescribed largest allowed prime B, a single explicit integer
is divisible by every odd perfect number supported in the interval. -/
theorem dvd_factorial_pow_of_bounded_support {N B : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hB : ∀ p ∈ N.primeFactors, p ≤ B) : N ∣ B.factorial ^ B := by
  apply (Nat.factorization_le_iff_dvd hN.2.ne' (pow_ne_zero _ (Nat.factorial_pos _).ne')).mp
  intro p
  by_cases hp : p ∈ N.primeFactors
  · obtain ⟨r, hr, hlt⟩ := exists_larger_prime_than_length hN ho hp
    have hrB := hB r (Finset.mem_of_mem_erase hr)
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hf := hprime.factorization_pos_of_dvd (Nat.factorial_pos B).ne'
      (Nat.dvd_factorial hprime.pos (hB p hp))
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact (show N.factorization p ≤ B by omega).trans (Nat.le_mul_of_pos_right _ hf)
  · have hz : N.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hz]

theorem finite_odd_perfect_of_bounded_support (B : ℕ) :
    Set.Finite {N : ℕ | Odd N ∧ N.Perfect ∧ ∀ p ∈ N.primeFactors, p ≤ B} := by
  apply (Set.finite_le_nat (B.factorial ^ B)).subset
  rintro N ⟨ho, hN, hB⟩
  exact Nat.le_of_dvd (pow_pos (Nat.factorial_pos _) _) (dvd_factorial_pow_of_bounded_support hN ho hB)

end OddPerfect
