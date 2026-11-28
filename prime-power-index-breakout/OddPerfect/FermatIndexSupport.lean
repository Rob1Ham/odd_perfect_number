module

public import OddPerfect.FermatIndex
public import Mathlib.Data.Nat.Squarefree
import OddPerfect.Cuts
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

private theorem odd_dvd_two_pow_eq_one {d k : ℕ} (hodd : Odd d) (hd : d ∣ 2^k) : d = 1 := by
  obtain ⟨t, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  by_cases ht : t = 0
  · simp [ht]
  · exact (hodd.not_two_dvd_nat (dvd_pow_self _ ht)).elim

/-- If all the other possible divisor-sum targets have power-of-two
multiplicative groups, then a Fermat prime `p` dividing the sum forces an
order-`p` prime at the remaining target `q`. -/
theorem index_prime_dvd_selected_pred {r e p q a i : ℕ}
    (hr : r.Prime) (he : Even e) (hp : p.Prime) (hpo : Odd p) (hq : q.Prime)
    (hpI : p ∣ i) (hi0 : i ≠ 0)
    (hsupp : ∀ u ∈ i.primeFactors, ∃ k : ℕ, u-1 = 2^k)
    (hout : sigma 1 (r^e) ∣ i*q^a) (hd : p ∣ sigma 1 (r^e)) : p ∣ q-1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (e+1) := Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)
  obtain ⟨k, hk⟩ := hsupp p (Nat.mem_primeFactors.mpr ⟨hp, hpI, hi0⟩)
  rw [sigma_one_apply, dvd_sum_divisors_prime_pow_iff hr hp] at hd
  have hlen : p ∣ e+1 := by
    by_cases h : (r : ZMod p) = 1
    · simpa [h] using hd
    · simp only [h, ite_false] at hd
      have hz : (r : ZMod p) ≠ 0 := by intro hz; rw [hz, orderOf_zero, zero_dvd_iff] at hd; omega
      have hgrp := ZMod.orderOf_dvd_card_sub_one hz
      rw [hk] at hgrp
      exact (h (orderOf_eq_one_iff.mp (odd_dvd_two_pow_eq_one (hodd.of_dvd_nat hd) hgrp))).elim
  obtain ⟨t, ht, hor, hpred⟩ := exists_prime_order_prime_pow hr.one_lt hp hpo 0
  simp only [zero_add, pow_one] at hor hpred
  have htne : (r : ZMod t) ≠ 1 := by intro h; simp [h] at hor; exact hp.ne_one hor.symm
  have htout : t ∣ sigma 1 (r^e) := by
    rw [sigma_one_apply, dvd_sum_divisors_prime_pow_iff hr ht]
    simpa [htne, hor] using hlen
  rcases ht.dvd_mul.mp (htout.trans hout) with hti | htq
  · obtain ⟨d, hd⟩ := hsupp t (Nat.mem_primeFactors.mpr ⟨ht, hti, hi0⟩)
    rw [hd] at hpred
    exact (hp.ne_one (odd_dvd_two_pow_eq_one hpo hpred)).elim
  · exact (Nat.prime_dvd_prime_iff_eq ht hq).mp (ht.dvd_of_dvd_pow htq) ▸ hpred

/-- For a squarefree Euler index supported on Fermat primes, every prime
divisor of the index divides the Euler length. -/
theorem squarefree_fermat_index_support_dvd_length {N q a m i : ℕ} (ho : Odd N)
    (hq : q.Prime) (hform : N = q^a*m^2) (hleft : sigma 1 (m^2) = q^a*i)
    (hright : sigma 1 (q^a)*i = 2*m^2) (hio : Odd i) (hsq : Squarefree i)
    (hsupp : ∀ u ∈ i.primeFactors, ∃ k : ℕ, u-1 = 2^k) :
    i.primeFactors ⊆ (a+1).primeFactors.erase 2 := by
  have hm := ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _))
  have hm2 := pow_ne_zero 2 hm.pos.ne'
  intro p hpI
  obtain ⟨hp, hpi, _⟩ := Nat.mem_primeFactors.mp hpI
  have hpo := hio.of_dvd_nat hpi
  have hp2 : p ≠ 2 := fun h => hpo.not_two_dvd_nat (h ▸ dvd_rfl)
  refine Finset.mem_erase.mpr ⟨hp2, Nat.mem_primeFactors.mpr ⟨hp, ?_, by omega⟩⟩
  have hpout : p ∣ sigma 1 (m^2) := hleft ▸ hpi.trans (dvd_mul_left _ _)
  have hprod := (isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hm2
  rw [hprod] at hpout
  obtain ⟨r, hrmem, hd⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpout
  let e := (m^2).factorization r
  have he : Even e := ⟨m.factorization r, by simp [e, Nat.factorization_pow, two_mul]⟩
  have hrσ : sigma 1 (r^e) ∣ i*q^a := by
    rw [Nat.mul_comm i, ← hleft, hprod]
    exact Finset.dvd_prod_of_mem _ hrmem
  have hcon := index_prime_dvd_selected_pred (Nat.prime_of_mem_primeFactors hrmem) he hp hpo hq
    hpi hio.pos.ne' hsupp hrσ hd
  have hq1 : q ≡ 1 [MOD p] := ((Nat.modEq_iff_dvd' hq.one_lt.le).mpr hcon).symm
  have hpD : p ∣ 2*m^2 := hright ▸ hpi.trans (dvd_mul_left _ _)
  have hpm := hp.dvd_of_dvd_pow ((Nat.coprime_two_right.mpr hpo).dvd_of_dvd_mul_left hpD)
  have hpS : p ∣ sigma 1 (q^a) := by
    by_contra h
    have hd2 : p^2 ∣ sigma 1 (q^a) * i :=
      hright ▸ (pow_dvd_pow_of_dvd hpm 2).trans (dvd_mul_left _ _)
    have hbad := ((hp.coprime_iff_not_dvd.mpr h).pow_left 2).dvd_of_dvd_mul_left hd2
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) (by simpa [pow_two] using hbad)
  exact ((sigma_modEq_of_one hq hq1 a).dvd_iff dvd_rfl).mp hpS

/-- A squarefree Euler index supported on Fermat primes has at least three
distinct prime divisors. -/
theorem three_le_squarefree_fermat_index_prime_count {N q a m i : ℕ} (hN : Nat.Perfect N)
    (ho : Odd N) (hq : q.Prime) (ha : Odd a) (hqm : ¬ q ∣ m) (hform : N = q^a*m^2)
    (hleft : sigma 1 (m^2) = q^a*i) (hright : sigma 1 (q^a)*i = 2*m^2)
    (hio : Odd i) (hsq : Squarefree i)
    (hsupp : ∀ u ∈ i.primeFactors, ∃ k : ℕ, u-1 = 2^k) : 3 ≤ i.primeFactors.card := by
  have hqb : ¬ q ∣ m^2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  have hcover := euler_prime_count_le_index_union hN ho hq ha hform hqb hleft hright
  rw [Finset.union_eq_left.mpr (squarefree_fermat_index_support_dvd_length ho hq hform hleft hright hio hsq hsupp)] at hcover
  have h2 : 2 ∈ (a+1).primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, by have := Nat.odd_iff.mp ha; omega, by omega⟩
  have hlen := Finset.card_erase_add_one h2
  have h := component_length_support_add_three_le hN ho hq ha.pos hform hqb
  have hcounts := (cardDistinctFactors_eq_cardFactors_iff_squarefree hio.pos.ne').mpr hsq
  rw [cardDistinctFactors_eq_card_primeFactors] at hcounts
  omega

/-- The Euler index is at least twenty-one, giving a corresponding strict
size inequality for the Euler prime power. -/
theorem euler_component_index_ge_twenty_one {N q a m : ℕ} (hN : Nat.Perfect N) (ho : Odd N)
    (hq : q.Prime) (ha : Odd a) (hqm : ¬ q ∣ m) (hform : N = q^a*m^2) :
    21 * q^a < 2*m^2 ∧ 21 ≤ sigma 1 (m^2) / q^a := by
  have hqb : ¬ q ∣ m^2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  obtain ⟨i, _, hleft, hright, _⟩ := exists_component_index hN hq hform hqb
  have hpar := component_index_parity_bound hN ho hq ha.pos hform hqb hleft hright
  obtain ⟨hio, hi3⟩ : Odd i ∧ 3 ≤ i := by
    rcases hpar with h | h
    · exact h.2
    · have := Nat.odd_iff.mp ha; have := Nat.even_iff.mp h.1; omega
  have hiP := component_index_not_prime hN ho hq ha.pos hform hqb hleft hright
  have hi9 := component_index_ne_fermat_prime_square hN ho hq ha.pos hform hqb hleft hright
    (p := 3) (k := 1) (by decide) (by decide)
  have hi15 : i ≠ 15 := by
    rintro rfl
    have hs : ∀ p ∈ (15 : ℕ).primeFactors, ∃ k : ℕ, p-1=2^k := by
      intro p hp
      have hf : (15 : ℕ).primeFactors = {3, 5} := by decide +kernel
      rw [hf, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    have := three_le_squarefree_fermat_index_prime_count hN ho hq ha hqm hform hleft hright
      hio ((Nat.squarefree_mul (by decide : Nat.Coprime 3 5)).mpr
        ⟨(by decide : Nat.Prime 3).squarefree, (by decide : Nat.Prime 5).squarefree⟩) hs
    have hcard : (15 : ℕ).primeFactors.card = 2 := by decide +kernel
    omega
  have hi21 : 21 ≤ i := by
    by_contra! h
    have check : ∀ x : Fin 21, Odd (x:ℕ) → 3 ≤ (x:ℕ) →
        (x:ℕ).Prime ∨ (x:ℕ) = 3^2 ∨ (x:ℕ) = 15 := by decide +kernel
    rcases check ⟨i,h⟩ hio hi3 with h | h | h
    · exact hiP h
    · exact hi9 h
    · exact hi15 h
  have hσ := self_lt_sigma_of_one_lt (one_lt_pow₀ hq.one_lt ha.pos.ne')
  refine ⟨?_, by rw [hleft, Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos)]; exact hi21⟩
  calc
    21 * q^a < 21 * sigma 1 (q^a) := Nat.mul_lt_mul_of_pos_left hσ (by decide)
    _ ≤ sigma 1 (q^a)*i := by rw [Nat.mul_comm 21]; exact Nat.mul_le_mul_left _ hi21
    _ = _ := hright

end OddPerfect
