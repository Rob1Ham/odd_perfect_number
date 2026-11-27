module

public import OddPerfect.HarmonicRoots
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect
open Finset

private theorem linear_le_prime_pow {r : ℕ} (hr : 1<r) (b : ℕ) :
    1+(r-1)*b ≤ r^b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have one := Nat.one_le_pow b r (by omega)
    rw [Nat.mul_succ,pow_succ]
    nlinarith [Nat.sub_add_cancel hr.le, Nat.mul_le_mul_left (r-1) one]

/-- If r^b divides the number of divisors, some component with r dividing
its exponent plus one must have a small prime base. This is independent
of harmonicity and applies to a residual coprime factor. -/
theorem small_base_of_dvd_divisor_count {m r b L : ℕ} (hm : 0<m) (hr : r.Prime) (hL : 0<L)
    (hd : r^b ∣ m.divisors.card) (cut : m < L^((r-1)*b)) :
    ∃ p ∈ m.primeFactors, p<L ∧ r ∣ m.factorization p + 1 := by
  by_contra! hn
  let v (p : ℕ) := (m.factorization p+1).factorization r
  have hτ : m.divisors.card ≠ 0 := (card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hm.ne'⟩).ne'
  have sum : b ≤ ∑ p ∈ m.primeFactors, v p := by
    have h := (hr.pow_dvd_iff_le_factorization hτ).mp hd
    rw [Nat.card_divisors hm.ne', Nat.factorization_prod_apply (by intros; omega)] at h
    exact h
  have localBound (p : ℕ) (hp : p ∈ m.primeFactors) : L^((r-1)*v p) ≤ p^(m.factorization p) := by
    by_cases hz : v p = 0
    · simpa only [hz,mul_zero,pow_zero] using
        (Nat.one_le_pow (m.factorization p) p (Nat.prime_of_mem_primeFactors hp).pos)
    · have hdiv := hr.dvd_iff_one_le_factorization (Nat.succ_ne_zero _) |>.mpr (Nat.pos_of_ne_zero hz)
      have hlp : L ≤ p := by
        by_contra! h
        exact hn p hp h hdiv
      have he := Nat.le_of_dvd (Nat.succ_pos (m.factorization p))
        (Nat.ordProj_dvd (m.factorization p+1) r)
      change r^(v p) ≤ m.factorization p+1 at he
      have := linear_le_prime_pow hr.one_lt (v p)
      exact (Nat.pow_le_pow_left hlp _).trans
        (Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos (by omega))
  apply cut.not_ge
  calc
    L^((r-1)*b) ≤ L^((r-1)*(∑ p ∈ m.primeFactors, v p)) :=
      Nat.pow_le_pow_right hL (Nat.mul_le_mul_left _ sum)
    _ = ∏ p ∈ m.primeFactors, L^((r-1)*v p) := by
      rw [Finset.mul_sum, Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ p ∈ m.primeFactors, p^m.factorization p :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) localBound
    _ = m := (Nat.prod_primeFactors_pow_factorization hm.ne').symm

end OddPerfect
