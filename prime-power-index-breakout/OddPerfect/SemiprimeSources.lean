module

public import OddPerfect.Reciprocal
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- Products over two distinct selected bases divide the full product. -/
theorem two_sources_mul_dvd_prod {S : Finset ℕ} {p r : ℕ} (hp : p ∈ S) (hr : r ∈ S)
    (hpr : p ≠ r) (f : ℕ → ℕ) : f p * f r ∣ ∏ t ∈ S, f t := by
  have hsub : ({p,r} : Finset ℕ) ⊆ S := by
    intro t h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl <;> assumption
  simpa [hpr] using Finset.prod_dvd_prod_of_subset {p,r} S f hsub

private theorem exists_unique_source_of_one_copy {S : Finset ℕ} (f : ℕ → ℕ) {p : ℕ}
    (hp : p.Prime) (hd : p ∣ ∏ t ∈ S, f t) (hsq : ¬ p^2 ∣ ∏ t ∈ S, f t) :
    ∃ x ∈ S, p ∣ f x ∧ ∀ t ∈ S, t ≠ x → ¬ p ∣ f t := by
  obtain ⟨x, hx, hpx⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
  refine ⟨x, hx, hpx, ?_⟩
  intro t ht htx hpt
  apply hsq
  rw [pow_two]
  exact (Nat.mul_dvd_mul hpt hpx).trans (two_sources_mul_dvd_prod ht hx htx f)

/-- Two distinct residual primes in the total divisor sum give at most two
exceptional sources; all other source sums are pure powers of `q`. -/
theorem exists_two_exceptional_sources {q a b p r : ℕ} (hb : 0 < b) (hq : q.Prime)
    (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) (hpq : p ≠ q) (hrq : r ≠ q)
    (hσ : sigma 1 b = q^a * (p*r)) :
    ∃ x ∈ b.primeFactors, ∃ y ∈ b.primeFactors,
      ∀ t ∈ b.primeFactors, t ≠ x → t ≠ y →
        ∃ β : ℕ, sigma 1 (t ^ b.factorization t) = q^β := by
  let f := fun t : ℕ => sigma 1 (t ^ b.factorization t)
  have hf : sigma 1 b = ∏ t ∈ b.primeFactors, f t :=
    (isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hb.ne'
  have unique (u v : ℕ) (hu : u.Prime) (hv : v.Prime) (huv : u ≠ v) (huq : u ≠ q)
      (hprod : ∏ t ∈ b.primeFactors, f t = q^a*(u*v)) :
      ∃ x ∈ b.primeFactors, u ∣ f x ∧ ∀ t ∈ b.primeFactors, t ≠ x → ¬ u ∣ f t := by
    apply exists_unique_source_of_one_copy f hu
    · rw [hprod]; exact (dvd_mul_right _ _).trans (dvd_mul_left _ _)
    · rw [hprod, pow_two, show q^a*(u*v) = u*(q^a*v) by ac_rfl]
      intro h
      rcases hu.dvd_mul.mp (Nat.dvd_of_mul_dvd_mul_left hu.pos h) with h | h
      · exact huq ((Nat.prime_dvd_prime_iff_eq hu hq).mp (hu.dvd_of_dvd_pow h))
      · exact huv ((Nat.prime_dvd_prime_iff_eq hu hv).mp h)
  obtain ⟨x, hx, _, hpx⟩ := unique p r hp hr hpr hpq (hf.symm.trans hσ)
  obtain ⟨y, hy, _, hry⟩ := unique r p hr hp hpr.symm hrq
    (by rw [Nat.mul_comm r, ← hσ, hf])
  refine ⟨x, hx, y, hy, ?_⟩
  intro t ht htx hty
  have hd : f t ∣ q^a*(p*r) := (hf.symm.trans hσ) ▸ Finset.dvd_prod_of_mem f ht
  have hcop := (hp.coprime_iff_not_dvd.mpr (hpx t ht htx)).symm.mul_right
    (hr.coprime_iff_not_dvd.mpr (hry t ht hty)).symm
  obtain ⟨β, _, hβ⟩ := (Nat.dvd_prime_pow hq).mp (hcop.dvd_of_dvd_mul_right hd)
  exact ⟨β,hβ⟩

/-- A prime that occurs once in an odd component index accounts for exactly
one of the exponents in the cofactor. -/
theorem one_copy_index_return_valuation {q a b i p : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hpo : Odd p) (hb : 0 < b) (hi : 0 < i) (hv : i.factorization p = 1)
    (hret : sigma 1 (q^a)*i = 2*b) :
    b.factorization p = (sigma 1 (q^a)).factorization p + 1 := by
  have h := congrArg (fun n : ℕ => n.factorization p) hret
  change (sigma 1 (q^a)*i).factorization p = (2*b).factorization p at h
  have hp2 : p ≠ 2 := fun h => hpo.not_two_dvd_nat (h ▸ dvd_rfl)
  rw [Nat.factorization_mul (sigma_pos _ _ (pow_ne_zero _ hq.ne_zero)).ne' hi.ne',
    Nat.factorization_mul (by decide : 2 ≠ 0) hb.ne', Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)), hv] at h
  omega

end OddPerfect
