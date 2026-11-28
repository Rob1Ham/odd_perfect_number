module

public import OddPerfect.IndexWeight
public import OddPerfect.ReciprocalValuation
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- An Euler length with at most five divisors equals twice any odd prime divisor. -/
theorem length_eq_twice_prime_of_five {a l : ℕ} (ha4 : a % 4 = 1) (hl : l.Prime) (hlo : Odd l)
    (hd : l ∣ a+1) (hc : (a+1).divisors.card ≤ 5) : a+1 = 2*l := by
  obtain ⟨u, hu⟩ : 2 ∣ a+1 := by omega
  have huo : Odd u := Nat.odd_iff.mpr (by omega)
  have hpos : 0 < u := huo.pos
  have hlu : l ∣ u := (Nat.coprime_two_right.mpr hlo).dvd_of_dvd_mul_left (hu ▸ hd)
  have hcount := Nat.Coprime.card_divisors_mul (Nat.coprime_two_right.mpr huo).symm
  rw [← hu] at hcount
  have h2 : (2:ℕ).divisors.card = 2 := by decide
  rw [h2] at hcount
  have hle := Nat.le_of_dvd hpos hlu
  by_contra h
  have hlt : l < u := by omega
  have hone := hl.one_lt
  have huone : u ≠ 1 := by omega
  have hsub : ({1, l, u} : Finset ℕ) ⊆ u.divisors := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Nat.one_mem_divisors.mpr hpos.ne'
    · exact Nat.mem_divisors.mpr ⟨hlu, hpos.ne'⟩
    · exact Nat.mem_divisors_self _ hpos.ne'
  have h3 : ({1, l, u} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [huone.symm, hl.ne_one.symm]),
      Finset.card_insert_of_notMem (by simp [hlt.ne]), Finset.card_singleton]
  have := Finset.card_le_card hsub
  omega

private theorem two_pow_exceeds_plus_three {n : ℕ} (hn : 3 ≤ n) : n+3 < 2^n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n _ ih => rw [pow_succ]; omega

/-- No component of an odd perfect number has index equal to the square of
a prime. The proof uses the five-prime bound and the return valuation at a
pure source whose length is forced to be twice that source prime. -/
theorem component_index_ne_prime_square {N q a b i p : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : Nat.Prime q) (ha : 0 < a) (hform : N = q^a*b) (hqb : ¬ q ∣ b)
    (hleft : sigma 1 b = q^a*i) (hright : sigma 1 (q^a)*i = 2*b)
    (hp : Nat.Prime p) : i ≠ p^2 := by
  rintro rfl
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b (q^a))
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hd : 4 ∣ 2*b := hright ▸ dvd_mul_left _ _
    have := hbo.not_two_dvd_nat
    omega
  have hpo := hp.odd_of_ne_two hp2
  have hao : Odd a := by
    rcases component_index_parity_bound hN ho hq ha hform hqb hleft hright with h | h
    · exact h.1
    · have := Nat.odd_iff.mp (hpo.pow (n := 2)); have := h.2.1; omega
  have hval : N.factorization q = a := by
    rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hbo.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hqb, hq.factorization_pow, Finsupp.single_eq_same, add_zero]
  obtain ⟨s, _, _, hs4, hoth⟩ := euler_exponents ho hN
  have hqs : q = s := by
    by_contra h
    have := Nat.even_iff.mp (hoth q h); have := Nat.odd_iff.mp hao; omega
  subst s
  have hbound := euler_prime_count_le_length_and_index_factors hN ho hq hao hform hqb hleft hright
  rw [Nat.primeFactors_pow _ (by decide : 2 ≠ 0), hp.primeFactors, Finset.card_singleton,
    cardFactors_apply_prime_pow hp] at hbound
  have hpow := two_pow_component_length_support_le_prime_count hN ho hq ha hform hqb
  have hN5 : N.primeFactors.card ≤ 5 := by
    by_contra! h
    have := two_pow_exceeds_plus_three (by omega : 3 ≤ (a+1).primeFactors.card)
    omega
  have hqN := Nat.mem_primeFactors.mpr ⟨hq, hform ▸ (dvd_pow_self q ha.ne').trans
    (dvd_mul_right _ _), hN.2.ne'⟩
  have hdiv := component_length_divisor_count hN ho hqN
  rw [hval] at hdiv
  have hpb := (Nat.coprime_two_right.mpr hpo).dvd_of_dvd_mul_left
    (show p ∣ 2*b from hright ▸ (dvd_pow_self p (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _))
  have hpq : p ≠ q := fun h => hqb (h ▸ hpb)
  let f := fun l : ℕ => sigma 1 (l ^ b.factorization l)
  let B := b.primeFactors.filter (fun l => p ∣ f l)
  have hprod : sigma 1 b = ∏ l ∈ b.primeFactors, f l :=
    (isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hbo.pos.ne'
  have hB : B.card ≤ 2 := by
    have hpB : p^B.card ∣ sigma 1 b := by
      rw [hprod, ← Finset.prod_const]
      exact (Finset.prod_dvd_prod_of_dvd _ _ (fun l hl => (Finset.mem_filter.mp hl).2)).trans
        (Finset.prod_dvd_prod_of_subset B b.primeFactors f (Finset.filter_subset _ _))
    rw [hleft] at hpB
    have hpq' := hp.coprime_iff_not_dvd.mpr (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
    have hd := ((hpq'.pow_left B.card).pow_right a).dvd_of_dvd_mul_left hpB
    have hv := (hp.pow_dvd_iff_le_factorization (pow_ne_zero 2 hp.ne_zero)).mp hd
    simpa [hp.factorization_pow] using hv
  obtain ⟨l, hlN, hlq, hlp, hlB⟩ : ∃ l ∈ N.primeFactors, l ≠ q ∧ l ≠ p ∧ l ∉ B := by
    by_contra! hn
    have hsub : N.primeFactors ⊆ insert q (insert p B) := by
      intro l hl
      rcases eq_or_ne l q with rfl | hlq
      · exact Finset.mem_insert_self ..
      rcases eq_or_ne l p with rfl | hlp
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hn l hl hlq hlp))
    have := Finset.card_le_card hsub
    have := Finset.card_insert_le q (insert p B)
    have := Finset.card_insert_le p B
    have := five_le_distinct_prime_factor_count ho hN
    omega
  obtain ⟨hl, hld, _⟩ := Nat.mem_primeFactors.mp hlN
  have hlnd : ¬ l ∣ q^a := fun h => hlq ((Nat.prime_dvd_prime_iff_eq hl hq).mp (hl.dvd_of_dvd_pow h))
  have hlb := (hl.dvd_mul.mp (hform ▸ hld)).resolve_left hlnd
  have hlmem := Nat.mem_primeFactors.mpr ⟨hl, hlb, hbo.pos.ne'⟩
  have hnotS : ¬ p ∣ f l := fun h => hlB (Finset.mem_filter.mpr ⟨hlmem, h⟩)
  have hpart : f l ∣ p^2 * q^a := by
    rw [Nat.mul_comm, ← hleft, hprod]; exact Finset.dvd_prod_of_mem _ hlmem
  have hsubq := ((hp.coprime_iff_not_dvd.mpr hnotS).symm.pow_right 2).dvd_of_dvd_mul_left hpart
  obtain ⟨β, _, hβ⟩ := (Nat.dvd_prime_pow hq).mp hsubq
  let e := b.factorization l
  have hepos : 0 < e := (hl.dvd_iff_one_le_factorization hbo.pos.ne').mp hlb
  have heq : N.factorization l = e := by
    rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hbo.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hlnd, zero_add]
  have hE : Even e := heq ▸ hoth l hlq
  have hlp' := hl.coprime_iff_not_dvd.mpr (fun h => hlp ((Nat.prime_dvd_prime_iff_eq hl hp).mp h))
  have hback : l^e ∣ sigma 1 (q^a) := ((hlp'.pow_left e).pow_right 2).dvd_of_dvd_mul_right
    (hright ▸ (Nat.ordProj_dvd b l).trans (dvd_mul_left _ _))
  have hlo := ho.of_dvd_nat hld
  have hrec := reciprocal_component_length hl hlo hq hepos hβ hback
  have hlen := (dvd_pow_self l (by have := Nat.even_iff.mp hE; omega : e-1 ≠ 0)).trans hrec
  have htwo := length_eq_twice_prime_of_five (hval ▸ hs4) hl hlo hlen (hdiv.trans hN5)
  exact not_pure_return_at_twice_source_length hl hlo hq hE hepos hβ hback htwo

/-- The prime-square exclusion for the index written as an explicit quotient. -/
theorem divisor_sum_component_index_ne_prime_square {N q a p : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : q.Prime) (ha : 0 < a) (hd : q^a ∣ N) (hex : ¬ q^(a+1) ∣ N)
    (hp : p.Prime) : sigma 1 (N / q^a) / q^a ≠ p^2 := by
  obtain ⟨b, hb⟩ := hd
  have hqb : ¬ q ∣ b := by
    intro h
    apply hex
    rw [hb, pow_succ]
    exact Nat.mul_dvd_mul_left _ h
  obtain ⟨i, _, hleft, hright, _⟩ := exists_component_index hN hq hb hqb
  rw [hb, Nat.mul_div_cancel_left b (Nat.pow_pos hq.pos), hleft,
    Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos)]
  exact component_index_ne_prime_square hN ho hq ha hb hqb hleft hright hp

end OddPerfect
