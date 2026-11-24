module

public import OddPerfect.IndexWeight
import OddPerfect.Cuts
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- With a single copy of the Euler prime in the divisor-sum product, removing
one component that supplies it leaves a product dividing the index. -/
theorem exists_erased_product_dvd_exponent_one_index {q b i : ℕ} (hq : q.Prime)
    (hb : 0<b) (hσ : sigma 1 b=q*i) :
    ∃ s ∈ b.primeFactors, (∏ r ∈ b.primeFactors.erase s, sigma 1 (r^b.factorization r)) ∣ i := by
  classical
  let f := fun r : ℕ => sigma 1 (r^b.factorization r)
  have hprod : (∏ r ∈ b.primeFactors, f r) = q*i :=
    ((isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hb.ne').symm.trans hσ
  have hqP : q ∣ ∏ r ∈ b.primeFactors, f r := hprod ▸ dvd_mul_right _ _
  obtain ⟨s,hs,hqs⟩ := (hq.prime.dvd_finsetProd_iff _).mp hqP
  obtain ⟨t,ht⟩ := hqs
  rw [← Finset.mul_prod_erase _ _ hs, ht, mul_assoc] at hprod
  have hI := Nat.eq_of_mul_eq_mul_left hq.pos hprod
  exact ⟨s,hs,hI ▸ dvd_mul_left _ _⟩

/-- The Euler index at exponent one is at least 22,971. This uses the three
smallest distinct odd primes for three components outside the source of `q`. -/
theorem euler_exponent_one_index_ge_22971 {N q m : ℕ} (hN : Nat.Perfect N) (ho : Odd N)
    (hq : q.Prime) (hqm : ¬q ∣ m) (hform : N=q*m^2) : 22971 ≤ sigma 1 (m^2)/q := by
  classical
  let b := m^2
  let f := fun r : ℕ => sigma 1 (r^b.factorization r)
  have hform' : N=q^1*b := by simpa [b]
  have hqb : ¬q ∣ b := fun h => hqm (hq.dvd_of_dvd_pow h)
  have hbo : Odd b := ho.of_dvd_nat (hform ▸ dvd_mul_left _ _)
  obtain ⟨i,hi,hleft,_,_⟩ := exists_component_index hN hq hform' hqb
  simp only [pow_one] at hleft
  obtain ⟨s,hs,hdiv⟩ := exists_erased_product_dvd_exponent_one_index hq hbo.pos hleft
  let S := b.primeFactors.erase s
  change (∏ r ∈ S, f r) ∣ i at hdiv
  have hN5 := five_le_distinct_prime_factor_count ho hN
  have hfac : N.primeFactors = {q} ∪ b.primeFactors := by rw [hform,Nat.primeFactors_mul hq.ne_zero hbo.pos.ne',hq.primeFactors]
  rw [hfac] at hN5
  have hgc := Finset.card_union_le ({q}:Finset ℕ) b.primeFactors
  rw [Finset.card_singleton] at hgc
  have her : S.card+1=b.primeFactors.card := Finset.card_erase_add_one hs
  have hthree : 3 ≤ S.card := by omega
  have prime (u : ℕ) (hu : u ∈ S) : u.Prime ∧ Odd u := by
    have hmem := Finset.mem_of_mem_erase hu
    exact ⟨Nat.prime_of_mem_primeFactors hmem, hbo.of_dvd_nat (Nat.dvd_of_mem_primeFactors hmem)⟩
  have hr : ∃ r ∈ S, 7 ≤ r := by
    by_contra! h
    have hsub : S ⊆ {3,5} := by
      intro u hu
      have hpr := (prime u hu).1.two_le
      have := Nat.odd_iff.mp (prime u hu).2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have := h u hu
      omega
    have := Finset.card_le_card hsub
    have hc : ({3,5}:Finset ℕ).card=2 := by decide
    omega
  obtain ⟨r,hr,hr7⟩ := hr
  have hcard1 := Finset.card_erase_add_one hr
  have ht : ∃ t ∈ S.erase r, 5 ≤ t := by
    by_contra! h
    have hsub : S.erase r ⊆ {3} := by
      intro u hu
      have hpr := (prime u (Finset.mem_of_mem_erase hu)).1.two_le
      have := Nat.odd_iff.mp (prime u (Finset.mem_of_mem_erase hu)).2
      simp only [Finset.mem_singleton]
      have := h u hu
      omega
    have := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at this
    omega
  obtain ⟨t,ht,ht5⟩ := ht
  have hcard2 := Finset.card_erase_add_one ht
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (by omega : 0 < ((S.erase r).erase t).card)
  obtain ⟨hvt,hvrS⟩ := Finset.mem_erase.mp hv
  obtain ⟨hvr,hvS⟩ := Finset.mem_erase.mp hvrS
  obtain ⟨htr,htS⟩ := Finset.mem_erase.mp ht
  have hv3 : 3 ≤ v := by have := (prime v hvS).1.two_le; have := Nat.odd_iff.mp (prime v hvS).2; omega
  have lower (u : ℕ) (hu : u ∈ S) : u^2+u+1 ≤ f u := by
    have huB := Finset.mem_of_mem_erase hu
    have hup := (prime u hu).1
    have hepos := (hup.dvd_iff_one_le_factorization hbo.pos.ne').mp (Nat.dvd_of_mem_primeFactors huB)
    have hv : b.factorization u=2*m.factorization u := by simp [b,Nat.factorization_pow]
    have hsub := Nat.divisors_subset_of_dvd (pow_ne_zero (b.factorization u) hup.ne_zero)
      (pow_dvd_pow u (by omega : 2 ≤ b.factorization u))
    have hs : sigma 1 (u^2) ≤ f u := by simpa [f,sigma_one_apply] using Finset.sum_le_sum_of_subset (f:=id) hsub
    rw [sigma_one_apply_prime_pow hup] at hs
    simpa [Finset.sum_range_succ,add_comm,add_assoc,add_left_comm] using hs
  have hsub : ({v,t,r}:Finset ℕ) ⊆ S := by
    intro u hu
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu
    rcases hu with rfl|rfl|rfl <;> assumption
  have hprod : f v*f t*f r ∣ i := by
    have := (Finset.prod_dvd_prod_of_subset _ _ f hsub).trans hdiv
    simpa [hvt,hvr,htr,mul_assoc] using this
  have hfv := lower v hvS
  have hft := lower t htS
  have hfr := lower r hr
  have mono {j u : ℕ} (h : j ≤ u) : j^2+j+1 ≤ u^2+u+1 :=
    Nat.add_le_add_right (Nat.add_le_add (Nat.pow_le_pow_left h 2) h) 1
  have hv13 : 13 ≤ f v := (mono hv3).trans hfv
  have ht31 : 31 ≤ f t := (mono ht5).trans hft
  have hr57 : 57 ≤ f r := (mono hr7).trans hfr
  change 22971 ≤ sigma 1 b/q
  rw [hleft,Nat.mul_div_cancel_left i hq.pos]
  exact (Nat.mul_le_mul (Nat.mul_le_mul hv13 ht31) hr57).trans (Nat.le_of_dvd hi hprod)

end OddPerfect
