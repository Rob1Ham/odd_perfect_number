module

public import OddPerfect.Cuts
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- Replacing uncompleted odd bases by their limiting factors cannot give
exact balance when an odd product has abundancy two. The finite index set
can include repeated bases. -/
theorem partial_product_ne_two {ι : Type*} [DecidableEq ι] (P c o : Finset ι)
    (base f g : ι → ℕ) (hc : c ⊂ P) (hop : o ⊆ P) (ho : Odd (P.prod f))
    (hb : ∀ i ∈ P, Odd (base i)) (hfg : ∀ i ∈ P, 0 < f i ∧ f i < g i)
    (hfull : P.prod g = 2 * P.prod f) :
    c.prod g * o.prod base ≠ 2 * c.prod f * ∏ i ∈ o, (base i - 1) := by
  rcases o.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp only [prod_empty, mul_one]
    let r := P \ c
    have hre : r.Nonempty := sdiff_nonempty.mpr hc.not_superset
    have hlt : r.prod f < r.prod g := prod_lt_prod_of_nonempty₀
      (fun q hq => (hfg q (mem_sdiff.mp hq).1).1)
      (fun q hq => (hfg q (mem_sdiff.mp hq).1).2) hre
    have hnf : r.prod f * c.prod f = P.prod f := prod_sdiff hc.subset
    have hng : r.prod g * c.prod g = 2 * P.prod f := (prod_sdiff hc.subset).trans hfull
    have hpos : 0 < c.prod f := prod_pos fun q hq => (hfg q (hc.subset hq)).1
    intro heq
    rw [heq] at hng
    nlinarith [Nat.mul_lt_mul_of_pos_right hlt hpos]
  · have hsum : c.prod g ∣ 2 * P.prod f := hfull ▸ prod_dvd_prod_of_subset c P g hc.subset
    have hoddprod : Odd (o.prod base) :=
      prod_induction base Odd (fun _ _ => Odd.mul) odd_one (fun i hi => hb i (hop hi))
    have h2 : 2 ∣ base p - 1 := by have := Nat.odd_iff.mp (hb p (hop hp)); omega
    obtain ⟨j, hj⟩ := h2.trans (dvd_prod_of_mem (fun i => base i - 1) hp)
    intro heq
    have hd : 4 ∣ c.prod g * o.prod base := by
      rw [heq, hj]
      exact ⟨c.prod f * j, by ring⟩
    have hcf : (o.prod base).Coprime 4 := by simpa using hoddprod.coprime_two_right.pow_right 2
    have h4 := (hcf.symm.dvd_of_dvd_mul_right hd).trans hsum
    exact ho.not_two_dvd_nat ((Nat.mul_dvd_mul_iff_left (a := 2) (by decide)).mp h4)

/-- The partial abundancy of the actual prime components of an odd perfect
number cannot equal two while a component remains unfinished. -/
theorem partial_abundancy_ne_two {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (c o : Finset ℕ) (hc : c ⊂ N.primeFactors) (hop : o ⊆ N.primeFactors) :
    (∏ p ∈ c, sigma 1 (p ^ N.factorization p)) * (∏ p ∈ o, p) ≠
      2 * (∏ p ∈ c, p ^ N.factorization p) * ∏ p ∈ o, (p - 1) := by
  let f := fun p => p ^ N.factorization p
  let g := fun p => sigma 1 (f p)
  have hf : N.primeFactors.prod f = N := (Nat.prod_primeFactors_pow_factorization hN.2.ne').symm
  apply partial_product_ne_two N.primeFactors c o id f g hc hop (hf.symm ▸ ho)
    (fun p hp => ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  · intro p hp
    have hgt : 1 < f p := one_lt_pow₀ (Nat.prime_of_mem_primeFactors hp).one_lt (Finsupp.mem_support_iff.mp hp)
    exact ⟨hgt.le, self_lt_sigma_of_one_lt hgt⟩
  · rw [hf, show N.primeFactors.prod g = sigma 1 N from
      (isMultiplicative_sigma.multiplicative_factorization _ hN.2.ne').symm, sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN

end OddPerfect
