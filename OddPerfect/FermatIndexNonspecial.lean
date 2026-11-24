module

public import OddPerfect.FermatIndexObstruction
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- If the other targets all have power-of-two predecessor, the complete
odd length is an order at the selected prime. -/
theorem full_length_at_selected_of_fermat_support {r q e a i : ℕ}
    (hr : r.Prime) (hro : Odd r) (hq : q.Prime) (he : Even e) (hpos : 0<e)
    (hi : i≠0) (hs : ∀ t ∈ i.primeFactors, ∃ k : ℕ, t-1=2^k)
    (hout : sigma 1 (r^e) ∣ q^a*i) :
    orderOf (r:ZMod q)=e+1 ∧ e+1 ∣ q-1 := by
  obtain ⟨t,ht,_,hord,hdiv⟩ := component_length_is_order_at_index_or_euler hr hro hq he hpos hi hout
  rcases Finset.mem_insert.mp ht with rfl|hI
  · exact ⟨hord,hdiv⟩
  · obtain ⟨k,hk⟩ := hs t hI
    obtain ⟨l,hl,hld⟩ := Nat.exists_prime_and_dvd (by omega : e+1≠1)
    have hlo := (show Odd (e+1) from Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)).of_dvd_nat hld
    rw [hk] at hdiv
    exact (hlo.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp
      (hl.dvd_of_dvd_pow (hld.trans hdiv))) ▸ dvd_rfl)).elim

/-- A fully Fermat-supported exact component index must select a
non-Fermat nonspecial prime of exponent at least the support size minus
two. Every even cofactor component realizes its full length at that prime. -/
theorem fermat_supported_component_structure {N q a b i : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hs : ∀ t ∈ i.primeFactors, ∃ k : ℕ, t-1=2^k) :
    Even a ∧ i%4=2 ∧ 4≤a ∧ N.primeFactors.card≤a+2 ∧
      (∀ k : ℕ, q-1≠2^k) ∧
      ∀ r ∈ b.primeFactors, Even (b.factorization r) →
        orderOf (r:ZMod q)=b.factorization r+1 ∧ b.factorization r+1 ∣ q-1 := by
  have hpar := (component_index_parity_bound hN ho hq ha hform hqb hl hr).resolve_left (by
    rintro ⟨_,hio,_⟩
    obtain ⟨p,hp,hbad⟩ := exists_nonfermat_prime_of_odd_component_index hN ho hq ha hform hqb hl hr hio
    obtain ⟨k,hk⟩ := hs p hp
    exact hbad k hk)
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hqo := ho.of_dvd_nat (hform ▸ (dvd_pow_self q ha.ne').trans (dvd_mul_right _ _))
  have hqi : ¬q ∣ i := fun hd => hqb ((Nat.coprime_two_right.mpr hqo).dvd_of_dvd_mul_left
    (hr ▸ hd.trans (dvd_mul_left _ _)))
  let f (r : ℕ) := sigma 1 (r^b.factorization r)
  let T := b.primeFactors.filter (fun r => Even (b.factorization r))
  have hprod : ∏ r ∈ b.primeFactors, f r = q^a*i :=
    ((isMultiplicative_sigma (k:=1)).multiplicative_factorization _ hbo.pos.ne').symm.trans hl
  have hlocal (r : ℕ) (hrT : r ∈ T) :
      q ∣ f r ∧ orderOf (r:ZMod q)=b.factorization r+1 ∧ b.factorization r+1 ∣ q-1 := by
    obtain ⟨hrb,he⟩ := Finset.mem_filter.mp hrT
    obtain ⟨hrp,hrs,_⟩ := Nat.mem_primeFactors.mp hrb
    have hpos := (hrp.dvd_iff_one_le_factorization hbo.pos.ne').mp hrs
    have hout : f r ∣ q^a*i := hprod ▸ Finset.dvd_prod_of_mem f hrb
    exact ⟨selected_dvd_component_of_fermat_index hrp hq he hpos (by omega) hs hout,
      full_length_at_selected_of_fermat_support hrp (hbo.of_dvd_nat hrs) hq he hpos (by omega) hs hout⟩
  have hpow : q^T.card ∣ q^a*i := by
    rw [←hprod,←Finset.prod_const]
    exact (Finset.prod_dvd_prod_of_dvd _ _ (fun r hrT => (hlocal r hrT).1)).trans
      (Finset.prod_dvd_prod_of_subset T b.primeFactors f (Finset.filter_subset _ _))
  have hcard := (hq.pow_dvd_iff_le_factorization (pow_ne_zero a hq.ne_zero)).mp
    (((hq.coprime_iff_not_dvd.mpr hqi).pow_left _).dvd_of_dvd_mul_right hpow)
  rw [hq.factorization_pow,Finsupp.single_eq_same] at hcard
  obtain ⟨s,_,_,_,hother⟩ := euler_exponents ho hN
  have hsub : N.primeFactors ⊆ insert q (insert s T) := by
    intro r hrN
    rcases eq_or_ne r q with rfl|hrq
    · exact Finset.mem_insert_self ..
    rcases eq_or_ne r s with rfl|hrs
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    obtain ⟨hrp,hrd,_⟩ := Nat.mem_primeFactors.mp hrN
    have hnot : ¬r ∣ q^a := fun h => hrq ((Nat.prime_dvd_prime_iff_eq hrp hq).mp (hrp.dvd_of_dvd_pow h))
    have hrb := (hrp.dvd_mul.mp (hform ▸ hrd)).resolve_left hnot
    have hv := hother r hrs
    rw [hform,Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hbo.pos.ne',Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnot,zero_add] at hv
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hrp,hrb,hbo.pos.ne'⟩,hv⟩))
  have hbound : N.primeFactors.card≤T.card+2 :=
    (Finset.card_le_card hsub).trans (by have := Finset.card_insert_le q (insert s T)
                                         have := Finset.card_insert_le s T
                                         omega)
  have hmin := five_le_distinct_prime_factor_count ho hN
  refine ⟨hpar.1,hpar.2.1,by have := Nat.even_iff.mp hpar.1; omega,by omega,?_,
    fun r hr he => (hlocal r (Finset.mem_filter.mpr ⟨hr,he⟩)).2⟩
  obtain ⟨r,hrT⟩ := Finset.card_pos.mp (by omega : 0<T.card)
  obtain ⟨hrb,he⟩ := Finset.mem_filter.mp hrT
  have hpos := ((Nat.prime_of_mem_primeFactors hrb).dvd_iff_one_le_factorization hbo.pos.ne').mp (Nat.dvd_of_mem_primeFactors hrb)
  obtain ⟨l,hlp,hld⟩ := Nat.exists_prime_and_dvd (by omega : b.factorization r+1≠1)
  have hlo := (show Odd (b.factorization r+1) from Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)).of_dvd_nat hld
  intro k hk
  have hd := hld.trans (hlocal r hrT).2.2
  rw [hk] at hd
  exact hlo.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).mp (hlp.dvd_of_dvd_pow hd)) ▸ dvd_rfl)

end OddPerfect
