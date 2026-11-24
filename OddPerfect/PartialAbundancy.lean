module

public import OddPerfect.Cuts
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- Complete a subset of the prime powers exactly and replace an arbitrary
second subset by its limiting factors p/(p−1). The resulting partial
abundancy cannot equal two as long as a true component remains unfinished. -/
theorem partial_abundancy_ne_two {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (c o : Finset ℕ) (hc : c ⊂ N.primeFactors) (hop : o ⊆ N.primeFactors) :
    (∏ p ∈ c, sigma 1 (p ^ N.factorization p)) * (∏ p ∈ o, p) ≠
      2 * (∏ p ∈ c, p ^ N.factorization p) * ∏ p ∈ o, (p - 1) := by
  let f := fun p => p ^ N.factorization p
  let g := fun p => sigma 1 (f p)
  change c.prod g * (∏ p ∈ o, p) ≠ 2 * c.prod f * ∏ p ∈ o, (p - 1)
  have hfull : N.primeFactors.prod g = 2 * N := by
    rw [show N.primeFactors.prod g = sigma 1 N from
      (isMultiplicative_sigma.multiplicative_factorization _ hN.2.ne').symm, sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN
  rcases o.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp only [prod_empty, mul_one]
    let r := N.primeFactors \ c
    have hre : r.Nonempty := sdiff_nonempty.mpr hc.not_superset
    have hf (q : ℕ) (hq : q ∈ N.primeFactors) : 1 < f q :=
      one_lt_pow₀ (Nat.prime_of_mem_primeFactors hq).one_lt (Finsupp.mem_support_iff.mp hq)
    have hlt : r.prod f < r.prod g :=
      prod_lt_prod_of_nonempty₀ (fun q hq => (hf q (mem_sdiff.mp hq).1).le)
        (fun q hq => self_lt_sigma_of_one_lt (hf q (mem_sdiff.mp hq).1)) hre
    have hnf : r.prod f * c.prod f = N := (prod_sdiff hc.subset).trans
      (Nat.prod_primeFactors_pow_factorization hN.2.ne').symm
    have hng : r.prod g * c.prod g = 2 * N := (prod_sdiff hc.subset).trans hfull
    have hpos : 0 < c.prod f := prod_pos (fun q hq => (hf q (hc.subset hq)).le)
    intro heq
    rw [heq] at hng
    nlinarith [Nat.mul_lt_mul_of_pos_right hlt hpos]
  · have hsum : c.prod g ∣ 2 * N :=
      hfull ▸ prod_dvd_prod_of_subset c N.primeFactors g hc.subset
    have hodd (q : ℕ) (hq : q ∈ o) : Odd q :=
      ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (hop hq))
    have hoddprod : Odd (∏ q ∈ o, q) :=
      prod_induction (fun q : ℕ => q) Odd (fun _ _ => Odd.mul) odd_one hodd
    have h2 : 2 ∣ p - 1 := by have := Nat.odd_iff.mp (hodd p hp); omega
    obtain ⟨j, hj⟩ := h2.trans (dvd_prod_of_mem (fun q => q - 1) hp)
    intro heq
    have hd : 4 ∣ c.prod g * (∏ q ∈ o, q) := by
      rw [heq, hj]
      exact ⟨c.prod f * j, by ring⟩
    have hcf : (∏ q ∈ o, q).Coprime 4 := by
      simpa using hoddprod.coprime_two_right.pow_right 2
    have h4 := (hcf.symm.dvd_of_dvd_mul_right hd).trans hsum
    exact ho.not_two_dvd_nat ((Nat.mul_dvd_mul_iff_left (a := 2) (by decide)).mp h4)

end OddPerfect
