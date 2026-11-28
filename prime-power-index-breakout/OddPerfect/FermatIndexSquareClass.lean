module

public import OddPerfect.FermatIndexSources
public import OddPerfect.Hirakawa
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- Every odd-length cofactor component sends a factor to the Euler prime
when all other possible targets have power-of-two predecessor. -/
theorem selected_dvd_component_of_fermat_index {p q e a i : ℕ} (hp : p.Prime) (hq : q.Prime)
    (he : Even e) (hepos : 0<e) (hi : 0 < i)
    (hs : ∀ r ∈ i.primeFactors, ∃ k : ℕ, r-1=2^k)
    (hout : sigma 1 (p^e) ∣ q^a*i) : q ∣ sigma 1 (p^e) := by
  obtain ⟨l,hl,hlen⟩ := Nat.exists_prime_and_dvd (by omega : e+1 ≠ 1)
  have hlo := (show Odd (e+1) from Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)).of_dvd_nat hlen
  obtain ⟨r,hr,horder,hpred⟩ := exists_prime_order_prime_pow hp.one_lt hl hlo 0
  simp only [zero_add,pow_one] at horder hpred
  have hne : (p : ZMod r) ≠ 1 := by intro h; rw [h,orderOf_one] at horder; exact hl.ne_one horder.symm
  have hd : r ∣ sigma 1 (p^e) := by
    rw [sigma_one_apply,dvd_sum_divisors_prime_pow_iff hp hr]; simpa [hne,horder] using hlen
  rcases hr.dvd_mul.mp (hd.trans hout) with hqD|hiD
  · exact (Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow hqD) ▸ hd
  · obtain ⟨k,hk⟩ := hs r (Nat.mem_primeFactors.mpr ⟨hr,hiD,hi.ne'⟩)
    rw [hk] at hpred
    exact (hlo.not_two_dvd_nat ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow hpred) ▸ dvd_rfl)).elim

/-- A Fermat-supported Euler index forces at least one copy of `q` for each
cofactor prime and hence `ω(N) ≤ a+1`. -/
theorem prime_count_le_length_of_fermat_supported_index {N q a m i : ℕ}
    (ho : Odd N) (hq : q.Prime) (ha : Odd a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hleft : sigma 1 (m^2)=q^a*i) (hret : sigma 1 (q^a)*i=2*m^2)
    (hs : ∀ r ∈ i.primeFactors, ∃ k : ℕ, r-1=2^k) : N.primeFactors.card ≤ a+1 := by
  let b := m^2
  let f := fun p : ℕ => sigma 1 (p^b.factorization p)
  have hbo : Odd b := ho.of_dvd_nat (hform ▸ dvd_mul_left _ _)
  have hipos : 0 < i := by
    by_contra! h
    have hz : i=0 := by omega
    rw [hz,mul_zero] at hleft
    have hσ := sigma_pos 1 _ hbo.pos.ne'
    change sigma 1 b=0 at hleft
    omega
  have hqo := ho.of_dvd_nat (hform ▸ (dvd_pow_self q ha.pos.ne').trans (dvd_mul_right _ _))
  have hqi : ¬q ∣ i := by
    intro hd
    exact hqm (hq.dvd_of_dvd_pow ((Nat.coprime_two_right.mpr hqo).dvd_of_dvd_mul_left (hret ▸ hd.trans (dvd_mul_left _ _))))
  have hprod : ∏ p ∈ b.primeFactors, f p = q^a*i :=
    ((isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hbo.pos.ne').symm.trans hleft
  have hall (p : ℕ) (hpB : p ∈ b.primeFactors) : q ∣ f p := by
    have hp := Nat.prime_of_mem_primeFactors hpB
    have he : b.factorization p=2*m.factorization p := by simp [b,Nat.factorization_pow]
    have hepos := (hp.dvd_iff_one_le_factorization hbo.pos.ne').mp (Nat.dvd_of_mem_primeFactors hpB)
    exact selected_dvd_component_of_fermat_index hp hq ⟨m.factorization p,by omega⟩ hepos hipos hs
      (hprod ▸ Finset.dvd_prod_of_mem f hpB)
  have hpow : q^b.primeFactors.card ∣ q^a*i := by
    rw [← hprod, ← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ hall
  have hc := (hq.pow_dvd_iff_le_factorization (pow_ne_zero a hq.ne_zero)).mp
    (((hq.coprime_iff_not_dvd.mpr hqi).pow_left _).dvd_of_dvd_mul_right hpow)
  rw [hq.factorization_pow,Finsupp.single_eq_same] at hc
  have hF : N.primeFactors={q} ∪ b.primeFactors := by
    rw [hform,Nat.primeFactors_mul (pow_ne_zero a hq.ne_zero) hbo.pos.ne',Nat.primeFactors_pow _ ha.pos.ne',hq.primeFactors]
  have hcard := Finset.card_union_le ({q}:Finset ℕ) b.primeFactors
  rw [Finset.card_singleton] at hcard
  rw [hF]
  omega

/-- Fermat-supported Euler indices have an odd prime of odd multiplicity
other than the possibility of a single such prime at three or five. -/
theorem fermat_supported_index_ne_small_prime_mul_square {N q a m i l t : ℕ} (hN : N.Perfect)
    (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hleft : sigma 1 (m^2)=q^a*i) (hret : sigma 1 (q^a)*i=2*m^2) (hio : Odd i)
    (hs : ∀ r ∈ i.primeFactors, ∃ k : ℕ, r-1=2^k) (hl : l=1 ∨ l=3 ∨ l=5) : i ≠ l*t^2 := by
  intro heq
  have ha : Odd a := Nat.odd_iff.mpr (by omega)
  have hc := prime_count_le_length_of_fermat_supported_index ho hq ha hqm hform hleft hret hs
  have := five_le_distinct_prime_factor_count ho hN
  have hag : 1<a := by omega
  have hquot : sigma 1 (m^2)/q^a=i := by rw [hleft,Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos)]
  rcases hl with h1|h35
  · subst l
    apply euler_index_not_square_of_exponent_gt_one hN ho hq hq4 ha4 hag hqm hform
    exact ⟨t,by rw [hquot,heq,one_mul,pow_two]⟩
  · have hlp : l.Prime := by rcases h35 with rfl|rfl <;> decide
    have hlo : Odd l := by rcases h35 with rfl|rfl <;> decide
    have hm := (ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _))).pos
    have hlI := Nat.mem_primeFactors.mpr ⟨hlp,heq ▸ dvd_mul_right _ _,hio.pos.ne'⟩
    obtain ⟨_,hv⟩ := fermat_supported_index_valuation hq hm hio hlI hs hleft hret
    have ht : t ≠ 0 := by intro h; simp [h] at heq; exact hio.pos.ne' heq
    rw [heq,Nat.factorization_mul hlp.ne_zero (pow_ne_zero 2 ht),Finsupp.add_apply,hlp.factorization_self,
      Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul] at hv
    have hd := (hlp.dvd_iff_one_le_factorization (by omega : a+1 ≠ 0)).mpr
      (by omega : 1 ≤ (a+1).factorization l)
    have hhalf := (Nat.coprime_two_right.mpr hlo).dvd_of_dvd_mul_left ((show a+1=2*((a+1)/2) by omega) ▸ hd)
    have hcase : q%16≠1 ∨ 3 ∣ (a+1)/2 ∨ 5 ∣ (a+1)/2 := by rcases h35 with rfl|rfl; exact .inr (.inl hhalf); exact .inr (.inr hhalf)
    exact euler_index_ne_prime_mul_square_of_residue_or_length hN ho hq hq4 ha4 hag hqm hform hcase l t (.inr hlp) (hquot.trans heq)

end OddPerfect
